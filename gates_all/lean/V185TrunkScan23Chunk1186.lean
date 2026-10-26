import V185TrunkScan23Chunk1185

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7026914 : List Nat := [3, 3, 4, 1, 1, 1, 10]
def baseStart_7026914 : Nat := 118140960795 + 7026914 * 2 ^ 59
def prefixEnd_7026914 : Nat := 4983230072969 + 3 ^ 40 * 7026914 * 2
def baseEnd_7026914 : Nat := 44545486417380560498257

theorem tailTrace_7026914 : CollatzResearch.WordTrace tailWord_7026914 prefixEnd_7026914 44545486417380560498257 := by
  unfold tailWord_7026914
  simp only [CollatzResearch.WordTrace]
  refine ⟨64073152216174538552839949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170861739243132102807573197 64073152216174538552839949)
  ·
    refine ⟨24027432081065451957314981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64073152216174538552839949 24027432081065451957314981)
    ·
      refine ⟨4505143515199772241996559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24027432081065451957314981 4505143515199772241996559)
      ·
        refine ⟨6757715272799658362994839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4505143515199772241996559 6757715272799658362994839)
        ·
          refine ⟨10136572909199487544492259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6757715272799658362994839 10136572909199487544492259)
          ·
            refine ⟨15204859363799231316738389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10136572909199487544492259 15204859363799231316738389)
            ·
              refine ⟨44545486417380560498257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15204859363799231316738389 44545486417380560498257)
              ·
                rfl

theorem cell23_7026914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 10].length) (baseStart_7026914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026914 prefixEnd_7026914 := by exact prefixLift 7026914
  have htrace : WordTrace (prefixWord ++ tailWord_7026914) baseStart_7026914 baseEnd_7026914 := by
    simpa [prefixWord, tailWord_7026914, baseEnd_7026914] using wordTrace_append hprefix tailTrace_7026914
  have hstable : (prefixWord ++ tailWord_7026914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026914).length < 2 ^ (prefixWord ++ tailWord_7026914).sum := by decide
  have hdescent : baseEnd_7026914 < baseStart_7026914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026923 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 4, 6]
def baseStart_7026923 : Nat := 118140960795 + 7026923 * 2 ^ 59
def prefixEnd_7026923 : Nat := 4983230072969 + 3 ^ 40 * 7026923 * 2
def baseEnd_7026923 : Nat := 1202729673711238621715425

theorem tailTrace_7026923 : CollatzResearch.WordTrace tailWord_7026923 prefixEnd_7026923 1202729673711238621715425 := by
  unfold tailWord_7026923
  simp only [CollatzResearch.WordTrace]
  refine ⟨256292937121665548748437423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170861958081110365832291615 256292937121665548748437423)
  ·
    refine ⟨384439405682498323122656135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256292937121665548748437423 384439405682498323122656135)
    ·
      refine ⟨576659108523747484683984203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384439405682498323122656135 576659108523747484683984203)
      ·
        refine ⟨864988662785621227025976305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576659108523747484683984203 864988662785621227025976305)
        ·
          refine ⟨648741497089215920269482229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 864988662785621227025976305 648741497089215920269482229)
          ·
            refine ⟨60819515352113992525263959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 648741497089215920269482229 60819515352113992525263959)
            ·
              refine ⟨91229273028170988787895939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60819515352113992525263959 91229273028170988787895939)
              ·
                refine ⟨136843909542256483181843909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91229273028170988787895939 136843909542256483181843909)
                ·
                  refine ⟨25658233039173090596595733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136843909542256483181843909 25658233039173090596595733)
                  ·
                    refine ⟨1202729673711238621715425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25658233039173090596595733 1202729673711238621715425)
                    ·
                      rfl

theorem cell23_7026923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 6].length) (baseStart_7026923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026923 prefixEnd_7026923 := by exact prefixLift 7026923
  have htrace : WordTrace (prefixWord ++ tailWord_7026923) baseStart_7026923 baseEnd_7026923 := by
    simpa [prefixWord, tailWord_7026923, baseEnd_7026923] using wordTrace_append hprefix tailTrace_7026923
  have hstable : (prefixWord ++ tailWord_7026923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026923).length < 2 ^ (prefixWord ++ tailWord_7026923).sum := by decide
  have hdescent : baseEnd_7026923 < baseStart_7026923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026940 : List Nat := [2, 2, 2, 1, 4, 1, 2, 1, 2, 6]
def baseStart_7026940 : Nat := 118140960795 + 7026940 * 2 ^ 59
def prefixEnd_7026940 : Nat := 4983230072969 + 3 ^ 40 * 7026940 * 2
def baseEnd_7026940 : Nat := 1202732583434947432877899

theorem tailTrace_7026940 : CollatzResearch.WordTrace tailWord_7026940 prefixEnd_7026940 1202732583434947432877899 := by
  unfold tailWord_7026940
  simp only [CollatzResearch.WordTrace]
  refine ⟨128146778581301980325903137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170862371441735973767870849 128146778581301980325903137)
  ·
    refine ⟨96110083935976485244427353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128146778581301980325903137 96110083935976485244427353)
    ·
      refine ⟨72082562951982363933320515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96110083935976485244427353 72082562951982363933320515)
      ·
        refine ⟨108123844427973545899980773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72082562951982363933320515 108123844427973545899980773)
        ·
          refine ⟨20273220830245039856246395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108123844427973545899980773 20273220830245039856246395)
          ·
            refine ⟨30409831245367559784369593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20273220830245039856246395 30409831245367559784369593)
            ·
              refine ⟨22807373434025669838277195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30409831245367559784369593 22807373434025669838277195)
              ·
                refine ⟨34211060151038504757415793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22807373434025669838277195 34211060151038504757415793)
                ·
                  refine ⟨25658295113278878568061845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34211060151038504757415793 25658295113278878568061845)
                  ·
                    refine ⟨1202732583434947432877899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25658295113278878568061845 1202732583434947432877899)
                    ·
                      rfl

theorem cell23_7026940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_7026940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026940 prefixEnd_7026940 := by exact prefixLift 7026940
  have htrace : WordTrace (prefixWord ++ tailWord_7026940) baseStart_7026940 baseEnd_7026940 := by
    simpa [prefixWord, tailWord_7026940, baseEnd_7026940] using wordTrace_append hprefix tailTrace_7026940
  have hstable : (prefixWord ++ tailWord_7026940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026940).length < 2 ^ (prefixWord ++ tailWord_7026940).sum := by decide
  have hdescent : baseEnd_7026940 < baseStart_7026940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027081 : List Nat := [1, 2, 1, 1, 6, 2, 2, 3, 1, 4]
def baseStart_7027081 : Nat := 118140960795 + 7027081 * 2 ^ 59
def prefixEnd_7027081 : Nat := 4983230072969 + 3 ^ 40 * 7027081 * 2
def baseEnd_7027081 : Nat := 1202756717025708748990183

theorem tailTrace_7027081 : CollatzResearch.WordTrace tailWord_7027081 prefixEnd_7027081 1202756717025708748990183 := by
  unfold tailWord_7027081
  simp only [CollatzResearch.WordTrace]
  refine ⟨256298699855093141732689097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170865799903395427821792731 256298699855093141732689097)
  ·
    refine ⟨192224024891319856299516823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256298699855093141732689097 192224024891319856299516823)
    ·
      refine ⟨288336037336979784449275235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192224024891319856299516823 288336037336979784449275235)
      ·
        refine ⟨432504056005469676673912853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288336037336979784449275235 432504056005469676673912853)
        ·
          refine ⟨20273627625256391094089665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 432504056005469676673912853 20273627625256391094089665)
          ·
            refine ⟨15205220718942293320567249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20273627625256391094089665 15205220718942293320567249)
            ·
              refine ⟨11403915539206719990425437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15205220718942293320567249 11403915539206719990425437)
              ·
                refine ⟨4276468327202519996409539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11403915539206719990425437 4276468327202519996409539)
                ·
                  refine ⟨6414702490803779994614309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4276468327202519996409539 6414702490803779994614309)
                  ·
                    refine ⟨1202756717025708748990183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6414702490803779994614309 1202756717025708748990183)
                    ·
                      rfl

theorem cell23_7027081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 1, 4].length) (baseStart_7027081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027081 prefixEnd_7027081 := by exact prefixLift 7027081
  have htrace : WordTrace (prefixWord ++ tailWord_7027081) baseStart_7027081 baseEnd_7027081 := by
    simpa [prefixWord, tailWord_7027081, baseEnd_7027081] using wordTrace_append hprefix tailTrace_7027081
  have hstable : (prefixWord ++ tailWord_7027081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027081).length < 2 ^ (prefixWord ++ tailWord_7027081).sum := by decide
  have hdescent : baseEnd_7027081 < baseStart_7027081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027104 : List Nat := [2, 1, 1, 4, 1, 3, 1, 3, 3, 1, 3]
def baseStart_7027104 : Nat := 118140960795 + 7027104 * 2 ^ 59
def prefixEnd_7027104 : Nat := 4983230072969 + 3 ^ 40 * 7027104 * 2
def baseEnd_7027104 : Nat := 3608281961132179656982943

theorem tailTrace_7027104 : CollatzResearch.WordTrace tailWord_7027104 prefixEnd_7027104 3608281961132179656982943 := by
  unfold tailWord_7027104
  simp only [CollatzResearch.WordTrace]
  refine ⟨128149769367004908330388183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170866359156006544440517577 128149769367004908330388183)
  ·
    refine ⟨192224654050507362495582275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128149769367004908330388183 192224654050507362495582275)
    ·
      refine ⟨288336981075761043743373413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192224654050507362495582275 288336981075761043743373413)
      ·
        refine ⟨54063183951705195701882515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 288336981075761043743373413 54063183951705195701882515)
        ·
          refine ⟨81094775927557793552823773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54063183951705195701882515 81094775927557793552823773)
          ·
            refine ⟨30410540972834172582308915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81094775927557793552823773 30410540972834172582308915)
            ·
              refine ⟨45615811459251258873463373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30410540972834172582308915 45615811459251258873463373)
              ·
                refine ⟨17105929297219222077548765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45615811459251258873463373 17105929297219222077548765)
                ·
                  refine ⟨6414723486457208279080787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17105929297219222077548765 6414723486457208279080787)
                  ·
                    refine ⟨9622085229685812418621181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6414723486457208279080787 9622085229685812418621181)
                    ·
                      refine ⟨3608281961132179656982943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9622085229685812418621181 3608281961132179656982943)
                      ·
                        rfl

theorem cell23_7027104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_7027104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027104 prefixEnd_7027104 := by exact prefixLift 7027104
  have htrace : WordTrace (prefixWord ++ tailWord_7027104) baseStart_7027104 baseEnd_7027104 := by
    simpa [prefixWord, tailWord_7027104, baseEnd_7027104] using wordTrace_append hprefix tailTrace_7027104
  have hstable : (prefixWord ++ tailWord_7027104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027104).length < 2 ^ (prefixWord ++ tailWord_7027104).sum := by decide
  have hdescent : baseEnd_7027104 < baseStart_7027104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027144 : List Nat := [2, 1, 3, 1, 3, 2, 2, 3, 1, 1, 4]
def baseStart_7027144 : Nat := 118140960795 + 7027144 * 2 ^ 59
def prefixEnd_7027144 : Nat := 4983230072969 + 3 ^ 40 * 7027144 * 2
def baseEnd_7027144 : Nat := 3608302500358359500482759

theorem tailTrace_7027144 : CollatzResearch.WordTrace tailWord_7027144 prefixEnd_7027144 3608302500358359500482759 := by
  unfold tailWord_7027144
  simp only [CollatzResearch.WordTrace]
  refine ⟨128150498826932451746116243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170867331769243268994821657 128150498826932451746116243)
  ·
    refine ⟨192225748240398677619174365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128150498826932451746116243 192225748240398677619174365)
    ·
      refine ⟨72084655590149504107190387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192225748240398677619174365 72084655590149504107190387)
      ·
        refine ⟨108126983385224256160785581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72084655590149504107190387 108126983385224256160785581)
        ·
          refine ⟨40547618769459096060294593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108126983385224256160785581 40547618769459096060294593)
          ·
            refine ⟨30410714077094322045220945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40547618769459096060294593 30410714077094322045220945)
            ·
              refine ⟨22808035557820741533915709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30410714077094322045220945 22808035557820741533915709)
              ·
                refine ⟨8553013334182778075218391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22808035557820741533915709 8553013334182778075218391)
                ·
                  refine ⟨12829520001274167112827587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8553013334182778075218391 12829520001274167112827587)
                  ·
                    refine ⟨19244280001911250669241381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12829520001274167112827587 19244280001911250669241381)
                    ·
                      refine ⟨3608302500358359500482759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19244280001911250669241381 3608302500358359500482759)
                      ·
                        rfl

theorem cell23_7027144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_7027144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027144 prefixEnd_7027144 := by exact prefixLift 7027144
  have htrace : WordTrace (prefixWord ++ tailWord_7027144) baseStart_7027144 baseEnd_7027144 := by
    simpa [prefixWord, tailWord_7027144, baseEnd_7027144] using wordTrace_append hprefix tailTrace_7027144
  have hstable : (prefixWord ++ tailWord_7027144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027144).length < 2 ^ (prefixWord ++ tailWord_7027144).sum := by decide
  have hdescent : baseEnd_7027144 < baseStart_7027144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027147 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 3]
def baseStart_7027147 : Nat := 118140960795 + 7027147 * 2 ^ 59
def prefixEnd_7027147 : Nat := 4983230072969 + 3 ^ 40 * 7027147 * 2
def baseEnd_7027147 : Nat := 3608304040800322988745245

theorem tailTrace_7027147 : CollatzResearch.WordTrace tailWord_7027147 prefixEnd_7027147 3608304040800322988745245 := by
  unfold tailWord_7027147
  simp only [CollatzResearch.WordTrace]
  refine ⟨256301107072854035004591695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170867404715236023336394463 256301107072854035004591695)
  ·
    refine ⟨384451660609281052506887543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256301107072854035004591695 384451660609281052506887543)
    ·
      refine ⟨576677490913921578760331315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384451660609281052506887543 576677490913921578760331315)
      ·
        refine ⟨865016236370882368140496973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576677490913921578760331315 865016236370882368140496973)
        ·
          refine ⟨324381088639080888052686365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 865016236370882368140496973 324381088639080888052686365)
          ·
            refine ⟨121642908239655333019757387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324381088639080888052686365 121642908239655333019757387)
            ·
              refine ⟨182464362359482999529636081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121642908239655333019757387 182464362359482999529636081)
              ·
                refine ⟨136848271769612249647227061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182464362359482999529636081 136848271769612249647227061)
                ·
                  refine ⟨12829525478401148404427537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136848271769612249647227061 12829525478401148404427537)
                  ·
                    refine ⟨9622144108800861303320653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12829525478401148404427537 9622144108800861303320653)
                    ·
                      refine ⟨3608304040800322988745245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9622144108800861303320653 3608304040800322988745245)
                      ·
                        rfl

theorem cell23_7027147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 3].length) (baseStart_7027147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027147 prefixEnd_7027147 := by exact prefixLift 7027147
  have htrace : WordTrace (prefixWord ++ tailWord_7027147) baseStart_7027147 baseEnd_7027147 := by
    simpa [prefixWord, tailWord_7027147, baseEnd_7027147] using wordTrace_append hprefix tailTrace_7027147
  have hstable : (prefixWord ++ tailWord_7027147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027147).length < 2 ^ (prefixWord ++ tailWord_7027147).sum := by decide
  have hdescent : baseEnd_7027147 < baseStart_7027147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027157 : List Nat := [1, 3, 2, 3, 1, 2, 1, 2, 1, 1, 6]
def baseStart_7027157 : Nat := 118140960795 + 7027157 * 2 ^ 59
def prefixEnd_7027157 : Nat := 4983230072969 + 3 ^ 40 * 7027157 * 2
def baseEnd_7027157 : Nat := 3608309175606867949620199

theorem tailTrace_7027157 : CollatzResearch.WordTrace tailWord_7027157 prefixEnd_7027157 3608309175606867949620199 := by
  unfold tailWord_7027157
  simp only [CollatzResearch.WordTrace]
  refine ⟨256301471802817806712455725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170867647868545204474970483 256301471802817806712455725)
  ·
    refine ⟨96113051926056677517170897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256301471802817806712455725 96113051926056677517170897)
    ·
      refine ⟨72084788944542508137878173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96113051926056677517170897 72084788944542508137878173)
      ·
        refine ⟨27031795854203440551704315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72084788944542508137878173 27031795854203440551704315)
        ·
          refine ⟨40547693781305160827556473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27031795854203440551704315 40547693781305160827556473)
          ·
            refine ⟨30410770335978870620667355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40547693781305160827556473 30410770335978870620667355)
            ·
              refine ⟨45616155503968305931001033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30410770335978870620667355 45616155503968305931001033)
              ·
                refine ⟨34212116627976229448250775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45616155503968305931001033 34212116627976229448250775)
                ·
                  refine ⟨51318174941964344172376163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34212116627976229448250775 51318174941964344172376163)
                  ·
                    refine ⟨76977262412946516258564245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51318174941964344172376163 76977262412946516258564245)
                    ·
                      refine ⟨3608309175606867949620199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76977262412946516258564245 3608309175606867949620199)
                      ·
                        rfl

theorem cell23_7027157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_7027157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027157 prefixEnd_7027157 := by exact prefixLift 7027157
  have htrace : WordTrace (prefixWord ++ tailWord_7027157) baseStart_7027157 baseEnd_7027157 := by
    simpa [prefixWord, tailWord_7027157, baseEnd_7027157] using wordTrace_append hprefix tailTrace_7027157
  have hstable : (prefixWord ++ tailWord_7027157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027157).length < 2 ^ (prefixWord ++ tailWord_7027157).sum := by decide
  have hdescent : baseEnd_7027157 < baseStart_7027157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027167 : List Nat := [1, 1, 2, 3, 3, 3, 2, 8]
def baseStart_7027167 : Nat := 118140960795 + 7027167 * 2 ^ 59
def prefixEnd_7027167 : Nat := 4983230072969 + 3 ^ 40 * 7027167 * 2
def baseEnd_7027167 : Nat := 133641270756052330018339

theorem tailTrace_7027167 : CollatzResearch.WordTrace tailWord_7027167 prefixEnd_7027167 133641270756052330018339 := by
  unfold tailWord_7027167
  simp only [CollatzResearch.WordTrace]
  refine ⟨256301836532781578420319755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170867891021854385613546503 256301836532781578420319755)
  ·
    refine ⟨384452754799172367630479633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256301836532781578420319755 384452754799172367630479633)
    ·
      refine ⟨288339566099379275722859725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384452754799172367630479633 288339566099379275722859725)
      ·
        refine ⟨108127337287267228396072397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288339566099379275722859725 108127337287267228396072397)
        ·
          refine ⟨40547751482725210648527149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108127337287267228396072397 40547751482725210648527149)
          ·
            refine ⟨15205406806021953993197681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40547751482725210648527149 15205406806021953993197681)
            ·
              refine ⟨11404055104516465494898261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15205406806021953993197681 11404055104516465494898261)
              ·
                refine ⟨133641270756052330018339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11404055104516465494898261 133641270756052330018339)
                ·
                  rfl

theorem cell23_7027167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 8].length) (baseStart_7027167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027167 prefixEnd_7027167 := by exact prefixLift 7027167
  have htrace : WordTrace (prefixWord ++ tailWord_7027167) baseStart_7027167 baseEnd_7027167 := by
    simpa [prefixWord, tailWord_7027167, baseEnd_7027167] using wordTrace_append hprefix tailTrace_7027167
  have hstable : (prefixWord ++ tailWord_7027167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027167).length < 2 ^ (prefixWord ++ tailWord_7027167).sum := by decide
  have hdescent : baseEnd_7027167 < baseStart_7027167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027171 : List Nat := [1, 1, 1, 6, 3, 1, 1, 3, 2, 4]
def baseStart_7027171 : Nat := 118140960795 + 7027171 * 2 ^ 59
def prefixEnd_7027171 : Nat := 4983230072969 + 3 ^ 40 * 7027171 * 2
def baseEnd_7027171 : Nat := 1202772121445343631615045

theorem tailTrace_7027171 : CollatzResearch.WordTrace tailWord_7027171 prefixEnd_7027171 1202772121445343631615045 := by
  unfold tailWord_7027171
  simp only [CollatzResearch.WordTrace]
  refine ⟨256301982424767087103465367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170867988283178058068976911 256301982424767087103465367)
  ·
    refine ⟨384452973637150630655198051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256301982424767087103465367 384452973637150630655198051)
    ·
      refine ⟨576679460455725945982797077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384452973637150630655198051 576679460455725945982797077)
      ·
        refine ⟨27031849708862153717943613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 576679460455725945982797077 27031849708862153717943613)
        ·
          refine ⟨10136943640823307644228855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27031849708862153717943613 10136943640823307644228855)
          ·
            refine ⟨15205415461234961466343283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10136943640823307644228855 15205415461234961466343283)
            ·
              refine ⟨22808123191852442199514925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15205415461234961466343283 22808123191852442199514925)
              ·
                refine ⟨8553046196944665824818097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22808123191852442199514925 8553046196944665824818097)
                ·
                  refine ⟨6414784647708499368613573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8553046196944665824818097 6414784647708499368613573)
                  ·
                    refine ⟨1202772121445343631615045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6414784647708499368613573 1202772121445343631615045)
                    ·
                      rfl

theorem cell23_7027171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 4].length) (baseStart_7027171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027171 prefixEnd_7027171 := by exact prefixLift 7027171
  have htrace : WordTrace (prefixWord ++ tailWord_7027171) baseStart_7027171 baseEnd_7027171 := by
    simpa [prefixWord, tailWord_7027171, baseEnd_7027171] using wordTrace_append hprefix tailTrace_7027171
  have hstable : (prefixWord ++ tailWord_7027171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027171).length < 2 ^ (prefixWord ++ tailWord_7027171).sum := by decide
  have hdescent : baseEnd_7027171 < baseStart_7027171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027181 : List Nat := [1, 5, 1, 3, 1, 2, 1, 1, 3, 2, 3]
def baseStart_7027181 : Nat := 118140960795 + 7027181 * 2 ^ 59
def prefixEnd_7027181 : Nat := 4983230072969 + 3 ^ 40 * 7027181 * 2
def baseEnd_7027181 : Nat := 3608321499142575855720089

theorem tailTrace_7027181 : CollatzResearch.WordTrace tailWord_7027181 prefixEnd_7027181 3608321499142575855720089 := by
  unfold tailWord_7027181
  simp only [CollatzResearch.WordTrace]
  refine ⟨256302347154730858811329397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170868231436487239207552931 256302347154730858811329397)
  ·
    refine ⟨24028345045756018013562131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 256302347154730858811329397 24028345045756018013562131)
    ·
      refine ⟨36042517568634027020343197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24028345045756018013562131 36042517568634027020343197)
      ·
        refine ⟨13515944088237760132628699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36042517568634027020343197 13515944088237760132628699)
        ·
          refine ⟨20273916132356640198943049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13515944088237760132628699 20273916132356640198943049)
          ·
            refine ⟨15205437099267480149207287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20273916132356640198943049 15205437099267480149207287)
            ·
              refine ⟨22808155648901220223810931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15205437099267480149207287 22808155648901220223810931)
              ·
                refine ⟨34212233473351830335716397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22808155648901220223810931 34212233473351830335716397)
                ·
                  refine ⟨12829587552506936375893649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34212233473351830335716397 12829587552506936375893649)
                  ·
                    refine ⟨9622190664380202281920237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12829587552506936375893649 9622190664380202281920237)
                    ·
                      refine ⟨3608321499142575855720089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9622190664380202281920237 3608321499142575855720089)
                      ·
                        rfl

theorem cell23_7027181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_7027181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027181 prefixEnd_7027181 := by exact prefixLift 7027181
  have htrace : WordTrace (prefixWord ++ tailWord_7027181) baseStart_7027181 baseEnd_7027181 := by
    simpa [prefixWord, tailWord_7027181, baseEnd_7027181] using wordTrace_append hprefix tailTrace_7027181
  have hstable : (prefixWord ++ tailWord_7027181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027181).length < 2 ^ (prefixWord ++ tailWord_7027181).sum := by decide
  have hdescent : baseEnd_7027181 < baseStart_7027181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027194 : List Nat := [3, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3]
def baseStart_7027194 : Nat := 118140960795 + 7027194 * 2 ^ 59
def prefixEnd_7027194 : Nat := 4983230072969 + 3 ^ 40 * 7027194 * 2
def baseEnd_7027194 : Nat := 3608328174391084304857529

theorem tailTrace_7027194 : CollatzResearch.WordTrace tailWord_7027194 prefixEnd_7027194 3608328174391084304857529 := by
  unfold tailWord_7027194
  simp only [CollatzResearch.WordTrace]
  refine ⟨64075705325920940507888159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170868547535789174687701757 64075705325920940507888159)
  ·
    refine ⟨96113557988881410761832239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64075705325920940507888159 96113557988881410761832239)
    ·
      refine ⟨144170336983322116142748359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96113557988881410761832239 144170336983322116142748359)
      ·
        refine ⟨216255505474983174214122539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144170336983322116142748359 216255505474983174214122539)
        ·
          refine ⟨324383258212474761321183809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216255505474983174214122539 324383258212474761321183809)
          ·
            refine ⟨243287443659356070990887857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324383258212474761321183809 243287443659356070990887857)
            ·
              refine ⟨182465582744517053243165893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243287443659356070990887857 182465582744517053243165893)
              ·
                refine ⟨34212296764596947483093605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182465582744517053243165893 34212296764596947483093605)
                ·
                  refine ⟨6414805643361927653080051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34212296764596947483093605 6414805643361927653080051)
                  ·
                    refine ⟨9622208465042891479620077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6414805643361927653080051 9622208465042891479620077)
                    ·
                      refine ⟨3608328174391084304857529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9622208465042891479620077 3608328174391084304857529)
                      ·
                        rfl

theorem cell23_7027194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3].length) (baseStart_7027194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027194 prefixEnd_7027194 := by exact prefixLift 7027194
  have htrace : WordTrace (prefixWord ++ tailWord_7027194) baseStart_7027194 baseEnd_7027194 := by
    simpa [prefixWord, tailWord_7027194, baseEnd_7027194] using wordTrace_append hprefix tailTrace_7027194
  have hstable : (prefixWord ++ tailWord_7027194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027194).length < 2 ^ (prefixWord ++ tailWord_7027194).sum := by decide
  have hdescent : baseEnd_7027194 < baseStart_7027194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027206 : List Nat := [6, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_7027206 : Nat := 118140960795 + 7027206 * 2 ^ 59
def prefixEnd_7027206 : Nat := 4983230072969 + 3 ^ 40 * 7027206 * 2
def baseEnd_7027206 : Nat := 3608334336158938257907475

theorem tailTrace_7027206 : CollatzResearch.WordTrace tailWord_7027206 prefixEnd_7027206 3608334336158938257907475 := by
  unfold tailWord_7027206
  simp only [CollatzResearch.WordTrace]
  refine ⟨8009476843113759002530921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 170868839319760192053992981 8009476843113759002530921)
  ·
    refine ⟨6007107632335319251898191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8009476843113759002530921 6007107632335319251898191)
    ·
      refine ⟨9010661448502978877847287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6007107632335319251898191 9010661448502978877847287)
      ·
        refine ⟨13515992172754468316770931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9010661448502978877847287 13515992172754468316770931)
        ·
          refine ⟨20273988259131702475156397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13515992172754468316770931 20273988259131702475156397)
          ·
            refine ⟨7602745597174388428183649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20273988259131702475156397 7602745597174388428183649)
            ·
              refine ⟨5702059197880791321137737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7602745597174388428183649 5702059197880791321137737)
              ·
                refine ⟨4276544398410593490853303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5702059197880791321137737 4276544398410593490853303)
                ·
                  refine ⟨6414816597615890236279955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4276544398410593490853303 6414816597615890236279955)
                  ·
                    refine ⟨9622224896423835354419933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6414816597615890236279955 9622224896423835354419933)
                    ·
                      refine ⟨3608334336158938257907475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9622224896423835354419933 3608334336158938257907475)
                      ·
                        rfl

theorem cell23_7027206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_7027206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027206 prefixEnd_7027206 := by exact prefixLift 7027206
  have htrace : WordTrace (prefixWord ++ tailWord_7027206) baseStart_7027206 baseEnd_7027206 := by
    simpa [prefixWord, tailWord_7027206, baseEnd_7027206] using wordTrace_append hprefix tailTrace_7027206
  have hstable : (prefixWord ++ tailWord_7027206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027206).length < 2 ^ (prefixWord ++ tailWord_7027206).sum := by decide
  have hdescent : baseEnd_7027206 < baseStart_7027206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027211 : List Nat := [1, 1, 1, 1, 7, 1, 1, 4, 2, 1, 3]
def baseStart_7027211 : Nat := 118140960795 + 7027211 * 2 ^ 59
def prefixEnd_7027211 : Nat := 4983230072969 + 3 ^ 40 * 7027211 * 2
def baseEnd_7027211 : Nat := 3608336903562210738344951

theorem tailTrace_7027211 : CollatzResearch.WordTrace tailWord_7027211 prefixEnd_7027211 3608336903562210738344951 := by
  unfold tailWord_7027211
  simp only [CollatzResearch.WordTrace]
  refine ⟨256303441344622173934921487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170868960896414782623280991 256303441344622173934921487)
  ·
    refine ⟨384455162016933260902382231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256303441344622173934921487 384455162016933260902382231)
    ·
      refine ⟨576682743025399891353573347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384455162016933260902382231 576682743025399891353573347)
      ·
        refine ⟨865024114538099837030360021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576682743025399891353573347 865024114538099837030360021)
        ·
          refine ⟨20274002684486714930399063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 865024114538099837030360021 20274002684486714930399063)
          ·
            refine ⟨30411004026730072395598595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20274002684486714930399063 30411004026730072395598595)
            ·
              refine ⟨45616506040095108593397893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30411004026730072395598595 45616506040095108593397893)
              ·
                refine ⟨8553094882517832861262105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45616506040095108593397893 8553094882517832861262105)
                ·
                  refine ⟨6414821161888374645946579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8553094882517832861262105 6414821161888374645946579)
                  ·
                    refine ⟨9622231742832561968919869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6414821161888374645946579 9622231742832561968919869)
                    ·
                      refine ⟨3608336903562210738344951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9622231742832561968919869 3608336903562210738344951)
                      ·
                        rfl

theorem cell23_7027211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 1, 3].length) (baseStart_7027211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027211 prefixEnd_7027211 := by exact prefixLift 7027211
  have htrace : WordTrace (prefixWord ++ tailWord_7027211) baseStart_7027211 baseEnd_7027211 := by
    simpa [prefixWord, tailWord_7027211, baseEnd_7027211] using wordTrace_append hprefix tailTrace_7027211
  have hstable : (prefixWord ++ tailWord_7027211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027211).length < 2 ^ (prefixWord ++ tailWord_7027211).sum := by decide
  have hdescent : baseEnd_7027211 < baseStart_7027211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027212 : List Nat := [2, 2, 1, 2, 4, 3, 2, 2, 1, 2, 2]
def baseStart_7027212 : Nat := 118140960795 + 7027212 * 2 ^ 59
def prefixEnd_7027212 : Nat := 4983230072969 + 3 ^ 40 * 7027212 * 2
def baseEnd_7027212 : Nat := 3608337417042865234432447

theorem tailTrace_7027212 : CollatzResearch.WordTrace tailWord_7027212 prefixEnd_7027212 3608337417042865234432447 := by
  unfold tailWord_7027212
  simp only [CollatzResearch.WordTrace]
  refine ⟨128151738908809275552853945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170868985211745700737138593 128151738908809275552853945)
  ·
    refine ⟨96113804181606956664640459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128151738908809275552853945 96113804181606956664640459)
    ·
      refine ⟨144170706272410434996960689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96113804181606956664640459 144170706272410434996960689)
      ·
        refine ⟨108128029704307826247720517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144170706272410434996960689 108128029704307826247720517)
        ·
          refine ⟨20274005569557717421447597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108128029704307826247720517 20274005569557717421447597)
          ·
            refine ⟨7602752088584144033042849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20274005569557717421447597 7602752088584144033042849)
            ·
              refine ⟨5702064066438108024782137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7602752088584144033042849 5702064066438108024782137)
              ·
                refine ⟨4276548049828581018586603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5702064066438108024782137 4276548049828581018586603)
                ·
                  refine ⟨6414822074742871527879905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4276548049828581018586603 6414822074742871527879905)
                  ·
                    refine ⟨4811116556057153645909929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6414822074742871527879905 4811116556057153645909929)
                    ·
                      refine ⟨3608337417042865234432447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4811116556057153645909929 3608337417042865234432447)
                      ·
                        rfl

theorem cell23_7027212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 1, 2, 2].length) (baseStart_7027212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027212 prefixEnd_7027212 := by exact prefixLift 7027212
  have htrace : WordTrace (prefixWord ++ tailWord_7027212) baseStart_7027212 baseEnd_7027212 := by
    simpa [prefixWord, tailWord_7027212, baseEnd_7027212] using wordTrace_append hprefix tailTrace_7027212
  have hstable : (prefixWord ++ tailWord_7027212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027212).length < 2 ^ (prefixWord ++ tailWord_7027212).sum := by decide
  have hdescent : baseEnd_7027212 < baseStart_7027212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027237 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 4, 1, 5]
def baseStart_7027237 : Nat := 118140960795 + 7027237 * 2 ^ 59
def prefixEnd_7027237 : Nat := 4983230072969 + 3 ^ 40 * 7027237 * 2
def baseEnd_7027237 : Nat := 3608350254059227636619831

theorem tailTrace_7027237 : CollatzResearch.WordTrace tailWord_7027237 prefixEnd_7027237 3608350254059227636619831 := by
  unfold tailWord_7027237
  simp only [CollatzResearch.WordTrace]
  refine ⟨256304389642527980375367965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170869593095018653583578643 256304389642527980375367965)
  ·
    refine ⟨96114146115947992640762987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256304389642527980375367965 96114146115947992640762987)
    ·
      refine ⟨144171219173921988961144481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96114146115947992640762987 144171219173921988961144481)
      ·
        refine ⟨108128414380441491720858361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144171219173921988961144481 108128414380441491720858361)
        ·
          refine ⟨81096310785331118790643771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108128414380441491720858361 81096310785331118790643771)
          ·
            refine ⟨121644466177996678185965657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81096310785331118790643771 121644466177996678185965657)
            ·
              refine ⟨91233349633497508639474243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121644466177996678185965657 91233349633497508639474243)
              ·
                refine ⟨136850024450246262959211365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91233349633497508639474243 136850024450246262959211365)
                ·
                  refine ⟨25659379584421174304852131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136850024450246262959211365 25659379584421174304852131)
                  ·
                    refine ⟨38489069376631761457278197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25659379584421174304852131 38489069376631761457278197)
                    ·
                      refine ⟨3608350254059227636619831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38489069376631761457278197 3608350254059227636619831)
                      ·
                        rfl

theorem cell23_7027237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_7027237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027237 prefixEnd_7027237 := by exact prefixLift 7027237
  have htrace : WordTrace (prefixWord ++ tailWord_7027237) baseStart_7027237 baseEnd_7027237 := by
    simpa [prefixWord, tailWord_7027237, baseEnd_7027237] using wordTrace_append hprefix tailTrace_7027237
  have hstable : (prefixWord ++ tailWord_7027237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027237).length < 2 ^ (prefixWord ++ tailWord_7027237).sum := by decide
  have hdescent : baseEnd_7027237 < baseStart_7027237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027251 : List Nat := [1, 1, 1, 2, 4, 2, 2, 2, 4, 2, 2]
def baseStart_7027251 : Nat := 118140960795 + 7027251 * 2 ^ 59
def prefixEnd_7027251 : Nat := 4983230072969 + 3 ^ 40 * 7027251 * 2
def baseEnd_7027251 : Nat := 3608357442788390581844767

theorem tailTrace_7027251 : CollatzResearch.WordTrace tailWord_7027251 prefixEnd_7027251 3608357442788390581844767 := by
  unfold tailWord_7027251
  simp only [CollatzResearch.WordTrace]
  refine ⟨256304900264477260766377607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170869933509651507177585071 256304900264477260766377607)
  ·
    refine ⟨384457350396715891149566411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256304900264477260766377607 384457350396715891149566411)
    ·
      refine ⟨576686025595073836724349617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384457350396715891149566411 576686025595073836724349617)
      ·
        refine ⟨432514519196305377543262213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 576686025595073836724349617 432514519196305377543262213)
        ·
          refine ⟨81096472349307258289361665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 432514519196305377543262213 81096472349307258289361665)
          ·
            refine ⟨60822354261980443717021249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81096472349307258289361665 60822354261980443717021249)
            ·
              refine ⟨45616765696485332787765937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60822354261980443717021249 45616765696485332787765937)
              ·
                refine ⟨34212574272363999590824453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45616765696485332787765937 34212574272363999590824453)
                ·
                  refine ⟨6414857676068249923279585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34212574272363999590824453 6414857676068249923279585)
                  ·
                    refine ⟨4811143257051187442459689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6414857676068249923279585 4811143257051187442459689)
                    ·
                      refine ⟨3608357442788390581844767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4811143257051187442459689 3608357442788390581844767)
                      ·
                        rfl

theorem cell23_7027251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 2, 2].length) (baseStart_7027251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027251 prefixEnd_7027251 := by exact prefixLift 7027251
  have htrace : WordTrace (prefixWord ++ tailWord_7027251) baseStart_7027251 baseEnd_7027251 := by
    simpa [prefixWord, tailWord_7027251, baseEnd_7027251] using wordTrace_append hprefix tailTrace_7027251
  have hstable : (prefixWord ++ tailWord_7027251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027251).length < 2 ^ (prefixWord ++ tailWord_7027251).sum := by decide
  have hdescent : baseEnd_7027251 < baseStart_7027251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027257 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 9]
def baseStart_7027257 : Nat := 118140960795 + 7027257 * 2 ^ 59
def prefixEnd_7027257 : Nat := 4983230072969 + 3 ^ 40 * 7027257 * 2
def baseEnd_7027257 : Nat := 400928947074701950929971

theorem tailTrace_7027257 : CollatzResearch.WordTrace tailWord_7027257 prefixEnd_7027257 400928947074701950929971 := by
  unfold tailWord_7027257
  simp only [CollatzResearch.WordTrace]
  refine ⟨256305119102455523791096025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170870079401637015860730683 256305119102455523791096025)
  ·
    refine ⟨192228839326841642843322019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256305119102455523791096025 192228839326841642843322019)
    ·
      refine ⟨288343258990262464264983029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192228839326841642843322019 288343258990262464264983029)
      ·
        refine ⟨27032180530337106024842159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 288343258990262464264983029 27032180530337106024842159)
        ·
          refine ⟨40548270795505659037263239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27032180530337106024842159 40548270795505659037263239)
          ·
            refine ⟨60822406193258488555894859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40548270795505659037263239 60822406193258488555894859)
            ·
              refine ⟨91233609289887732833842289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60822406193258488555894859 91233609289887732833842289)
              ·
                refine ⟨68425206967415799625381717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91233609289887732833842289 68425206967415799625381717)
                ·
                  refine ⟨400928947074701950929971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68425206967415799625381717 400928947074701950929971)
                  ·
                    rfl

theorem cell23_7027257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 9].length) (baseStart_7027257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027257 prefixEnd_7027257 := by exact prefixLift 7027257
  have htrace : WordTrace (prefixWord ++ tailWord_7027257) baseStart_7027257 baseEnd_7027257 := by
    simpa [prefixWord, tailWord_7027257, baseEnd_7027257] using wordTrace_append hprefix tailTrace_7027257
  have hstable : (prefixWord ++ tailWord_7027257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027257).length < 2 ^ (prefixWord ++ tailWord_7027257).sum := by decide
  have hdescent : baseEnd_7027257 < baseStart_7027257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027262 : List Nat := [4, 2, 1, 4, 1, 2, 1, 2, 2, 1, 3]
def baseStart_7027262 : Nat := 118140960795 + 7027262 * 2 ^ 59
def prefixEnd_7027262 : Nat := 4983230072969 + 3 ^ 40 * 7027262 * 2
def baseEnd_7027262 : Nat := 3608363091075590038807217

theorem tailTrace_7027262 : CollatzResearch.WordTrace tailWord_7027262 prefixEnd_7027262 3608363091075590038807217 := by
  unfold tailWord_7027262
  simp only [CollatzResearch.WordTrace]
  refine ⟨32038162683429676205628505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170870200978291606430018693 32038162683429676205628505)
  ·
    refine ⟨24028622012572257154221379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32038162683429676205628505 24028622012572257154221379)
    ·
      refine ⟨36042933018858385731332069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24028622012572257154221379 36042933018858385731332069)
      ·
        refine ⟨6758049941035947324624763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36042933018858385731332069 6758049941035947324624763)
        ·
          refine ⟨10137074911553920986937145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6758049941035947324624763 10137074911553920986937145)
          ·
            refine ⟨7602806183665440740202859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10137074911553920986937145 7602806183665440740202859)
            ·
              refine ⟨11404209275498161110304289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7602806183665440740202859 11404209275498161110304289)
              ·
                refine ⟨8553156956623620832728217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11404209275498161110304289 8553156956623620832728217)
                ·
                  refine ⟨6414867717467715624546163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8553156956623620832728217 6414867717467715624546163)
                  ·
                    refine ⟨9622301576201573436819245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6414867717467715624546163 9622301576201573436819245)
                    ·
                      refine ⟨3608363091075590038807217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9622301576201573436819245 3608363091075590038807217)
                      ·
                        rfl

theorem cell23_7027262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_7027262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027262 prefixEnd_7027262 := by exact prefixLift 7027262
  have htrace : WordTrace (prefixWord ++ tailWord_7027262) baseStart_7027262 baseEnd_7027262 := by
    simpa [prefixWord, tailWord_7027262, baseEnd_7027262] using wordTrace_append hprefix tailTrace_7027262
  have hstable : (prefixWord ++ tailWord_7027262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027262).length < 2 ^ (prefixWord ++ tailWord_7027262).sum := by decide
  have hdescent : baseEnd_7027262 < baseStart_7027262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027274 : List Nat := [3, 1, 2, 1, 1, 5, 2, 1, 7]
def baseStart_7027274 : Nat := 118140960795 + 7027274 * 2 ^ 59
def prefixEnd_7027274 : Nat := 4983230072969 + 3 ^ 40 * 7027274 * 2
def baseEnd_7027274 : Nat := 400929916982604887984129

theorem tailTrace_7027274 : CollatzResearch.WordTrace tailWord_7027274 prefixEnd_7027274 400929916982604887984129 := by
  unfold tailWord_7027274
  simp only [CollatzResearch.WordTrace]
  refine ⟨64076434785848483923616219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170870492762262623796309917 64076434785848483923616219)
  ·
    refine ⟨96114652178772725885424329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64076434785848483923616219 96114652178772725885424329)
    ·
      refine ⟨72085989134079544414068247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96114652178772725885424329 72085989134079544414068247)
      ·
        refine ⟨108128983701119316621102371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72085989134079544414068247 108128983701119316621102371)
        ·
          refine ⟨162193475551678974931653557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108128983701119316621102371 162193475551678974931653557)
          ·
            refine ⟨15205638332969903899842521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162193475551678974931653557 15205638332969903899842521)
            ·
              refine ⟨11404228749727427924881891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15205638332969903899842521 11404228749727427924881891)
              ·
                refine ⟨17106343124591141887322837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11404228749727427924881891 17106343124591141887322837)
                ·
                  refine ⟨400929916982604887984129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17106343124591141887322837 400929916982604887984129)
                  ·
                    rfl

theorem cell23_7027274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 7].length) (baseStart_7027274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027274 prefixEnd_7027274 := by exact prefixLift 7027274
  have htrace : WordTrace (prefixWord ++ tailWord_7027274) baseStart_7027274 baseEnd_7027274 := by
    simpa [prefixWord, tailWord_7027274, baseEnd_7027274] using wordTrace_append hprefix tailTrace_7027274
  have hstable : (prefixWord ++ tailWord_7027274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027274).length < 2 ^ (prefixWord ++ tailWord_7027274).sum := by decide
  have hdescent : baseEnd_7027274 < baseStart_7027274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027287 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 3, 7]
def baseStart_7027287 : Nat := 118140960795 + 7027287 * 2 ^ 59
def prefixEnd_7027287 : Nat := 4983230072969 + 3 ^ 40 * 7027287 * 2
def baseEnd_7027287 : Nat := 1202791976030650813664867

theorem tailTrace_7027287 : CollatzResearch.WordTrace tailWord_7027287 prefixEnd_7027287 1202791976030650813664867 := by
  unfold tailWord_7027287
  simp only [CollatzResearch.WordTrace]
  refine ⟨256306213292346838914688115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170870808861564559276458743 256306213292346838914688115)
  ·
    refine ⟨384459319938520258372032173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256306213292346838914688115 384459319938520258372032173)
    ·
      refine ⟨144172244976945096889512065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384459319938520258372032173 144172244976945096889512065)
      ·
        refine ⟨108129183732708822667134049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144172244976945096889512065 108129183732708822667134049)
        ·
          refine ⟨81096887799531617000350537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108129183732708822667134049 81096887799531617000350537)
          ·
            refine ⟨60822665849648712750262903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81096887799531617000350537 60822665849648712750262903)
            ·
              refine ⟨91233998774473069125394355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60822665849648712750262903 91233998774473069125394355)
              ·
                refine ⟨136850998161709603688091533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91233998774473069125394355 136850998161709603688091533)
                ·
                  refine ⟨51319124310641101383034325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136850998161709603688091533 51319124310641101383034325)
                  ·
                    refine ⟨1202791976030650813664867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51319124310641101383034325 1202791976030650813664867)
                    ·
                      rfl

theorem cell23_7027287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_7027287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027287 prefixEnd_7027287 := by exact prefixLift 7027287
  have htrace : WordTrace (prefixWord ++ tailWord_7027287) baseStart_7027287 baseEnd_7027287 := by
    simpa [prefixWord, tailWord_7027287, baseEnd_7027287] using wordTrace_append hprefix tailTrace_7027287
  have hstable : (prefixWord ++ tailWord_7027287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027287).length < 2 ^ (prefixWord ++ tailWord_7027287).sum := by decide
  have hdescent : baseEnd_7027287 < baseStart_7027287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027324 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 4, 1, 4]
def baseStart_7027324 : Nat := 118140960795 + 7027324 * 2 ^ 59
def prefixEnd_7027324 : Nat := 4983230072969 + 3 ^ 40 * 7027324 * 2
def baseEnd_7027324 : Nat := 3608394926876168796231931

theorem tailTrace_7027324 : CollatzResearch.WordTrace tailWord_7027324 prefixEnd_7027324 3608394926876168796231931 := by
  unfold tailWord_7027324
  simp only [CollatzResearch.WordTrace]
  refine ⟨128153781396606397116892513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170871708528808529489190017 128153781396606397116892513)
  ·
    refine ⟨96115336047454797837669385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128153781396606397116892513 96115336047454797837669385)
    ·
      refine ⟨72086502035591098378252039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96115336047454797837669385 72086502035591098378252039)
      ·
        refine ⟨108129753053386647567378059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72086502035591098378252039 108129753053386647567378059)
        ·
          refine ⟨162194629580079971351067089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108129753053386647567378059 162194629580079971351067089)
          ·
            refine ⟨121645972185059978513300317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162194629580079971351067089 121645972185059978513300317)
            ·
              refine ⟨45617239569397491942487619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121645972185059978513300317 45617239569397491942487619)
              ·
                refine ⟨68425859354096237913731429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45617239569397491942487619 68425859354096237913731429)
                ·
                  refine ⟨12829848628893044608824643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68425859354096237913731429 12829848628893044608824643)
                  ·
                    refine ⟨19244772943339566913236965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12829848628893044608824643 19244772943339566913236965)
                    ·
                      refine ⟨3608394926876168796231931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19244772943339566913236965 3608394926876168796231931)
                      ·
                        rfl

theorem cell23_7027324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_7027324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027324 prefixEnd_7027324 := by exact prefixLift 7027324
  have htrace : WordTrace (prefixWord ++ tailWord_7027324) baseStart_7027324 baseEnd_7027324 := by
    simpa [prefixWord, tailWord_7027324, baseEnd_7027324] using wordTrace_append hprefix tailTrace_7027324
  have hstable : (prefixWord ++ tailWord_7027324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027324).length < 2 ^ (prefixWord ++ tailWord_7027324).sum := by decide
  have hdescent : baseEnd_7027324 < baseStart_7027324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027327 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 5]
def baseStart_7027327 : Nat := 118140960795 + 7027327 * 2 ^ 59
def prefixEnd_7027327 : Nat := 4983230072969 + 3 ^ 40 * 7027327 * 2
def baseEnd_7027327 : Nat := 3608396467318132284494417

theorem tailTrace_7027327 : CollatzResearch.WordTrace tailWord_7027327 prefixEnd_7027327 3608396467318132284494417 := by
  unfold tailWord_7027327
  simp only [CollatzResearch.WordTrace]
  refine ⟨256307672212201925746144235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170871781474801283830762823 256307672212201925746144235)
  ·
    refine ⟨384461508318302888619216353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256307672212201925746144235 384461508318302888619216353)
    ·
      refine ⟨288346131238727166464412265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384461508318302888619216353 288346131238727166464412265)
      ·
        refine ⟨216259598429045374848309199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288346131238727166464412265 216259598429045374848309199)
        ·
          refine ⟨324389397643568062272463799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216259598429045374848309199 324389397643568062272463799)
          ·
            refine ⟨486584096465352093408695699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324389397643568062272463799 486584096465352093408695699)
            ·
              refine ⟨729876144698028140113043549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486584096465352093408695699 729876144698028140113043549)
              ·
                refine ⟨273703554261760552542391331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 729876144698028140113043549 273703554261760552542391331)
                ·
                  refine ⟨410555331392640828813586997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 273703554261760552542391331 410555331392640828813586997)
                  ·
                    refine ⟨38489562318060077701273781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 410555331392640828813586997 38489562318060077701273781)
                    ·
                      refine ⟨3608396467318132284494417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38489562318060077701273781 3608396467318132284494417)
                      ·
                        rfl

theorem cell23_7027327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_7027327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027327 prefixEnd_7027327 := by exact prefixLift 7027327
  have htrace : WordTrace (prefixWord ++ tailWord_7027327) baseStart_7027327 baseEnd_7027327 := by
    simpa [prefixWord, tailWord_7027327, baseEnd_7027327] using wordTrace_append hprefix tailTrace_7027327
  have hstable : (prefixWord ++ tailWord_7027327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027327).length < 2 ^ (prefixWord ++ tailWord_7027327).sum := by decide
  have hdescent : baseEnd_7027327 < baseStart_7027327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027358 : List Nat := [4, 3, 1, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_7027358 : Nat := 118140960795 + 7027358 * 2 ^ 59
def prefixEnd_7027358 : Nat := 4983230072969 + 3 ^ 40 * 7027358 * 2
def baseEnd_7027358 : Nat := 3608412385218421663206775

theorem tailTrace_7027358 : CollatzResearch.WordTrace tailWord_7027358 prefixEnd_7027358 3608412385218421663206775 := by
  unfold tailWord_7027358
  simp only [CollatzResearch.WordTrace]
  refine ⟨32038600359386202255065341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170872535250059745360348485 32038600359386202255065341)
  ·
    refine ⟨12014475134769825845649503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32038600359386202255065341 12014475134769825845649503)
    ·
      refine ⟨18021712702154738768474255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12014475134769825845649503 18021712702154738768474255)
      ·
        refine ⟨27032569053232108152711383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18021712702154738768474255 27032569053232108152711383)
        ·
          refine ⟨40548853579848162229067075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27032569053232108152711383 40548853579848162229067075)
          ·
            refine ⟨60823280369772243343600613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40548853579848162229067075 60823280369772243343600613)
            ·
              refine ⟨11404365069332295626925115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60823280369772243343600613 11404365069332295626925115)
              ·
                refine ⟨17106547603998443440387673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11404365069332295626925115 17106547603998443440387673)
                ·
                  refine ⟨12829910702998832580290755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17106547603998443440387673 12829910702998832580290755)
                  ·
                    refine ⟨19244866054498248870436133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12829910702998832580290755 19244866054498248870436133)
                    ·
                      refine ⟨3608412385218421663206775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19244866054498248870436133 3608412385218421663206775)
                      ·
                        rfl

theorem cell23_7027358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_7027358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027358 prefixEnd_7027358 := by exact prefixLift 7027358
  have htrace : WordTrace (prefixWord ++ tailWord_7027358) baseStart_7027358 baseEnd_7027358 := by
    simpa [prefixWord, tailWord_7027358, baseEnd_7027358] using wordTrace_append hprefix tailTrace_7027358
  have hstable : (prefixWord ++ tailWord_7027358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027358).length < 2 ^ (prefixWord ++ tailWord_7027358).sum := by decide
  have hdescent : baseEnd_7027358 < baseStart_7027358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027381 : List Nat := [1, 3, 3, 3, 1, 1, 1, 4, 6]
def baseStart_7027381 : Nat := 118140960795 + 7027381 * 2 ^ 59
def prefixEnd_7027381 : Nat := 4983230072969 + 3 ^ 40 * 7027381 * 2
def baseEnd_7027381 : Nat := 400936021697052785913241

theorem tailTrace_7027381 : CollatzResearch.WordTrace tailWord_7027381 prefixEnd_7027381 400936021697052785913241 := by
  unfold tailWord_7027381
  simp only [CollatzResearch.WordTrace]
  refine ⟨256309641754006292968609997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170873094502670861979073331 256309641754006292968609997)
  ·
    refine ⟨96116115657752359863228749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256309641754006292968609997 96116115657752359863228749)
    ·
      refine ⟨36043543371657134948710781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96116115657752359863228749 36043543371657134948710781)
      ·
        refine ⟨13516328764371425605766543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36043543371657134948710781 13516328764371425605766543)
        ·
          refine ⟨20274493146557138408649815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13516328764371425605766543 20274493146557138408649815)
          ·
            refine ⟨30411739719835707612974723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20274493146557138408649815 30411739719835707612974723)
            ·
              refine ⟨45617609579753561419462085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30411739719835707612974723 45617609579753561419462085)
              ·
                refine ⟨8553301796203792766149141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45617609579753561419462085 8553301796203792766149141)
                ·
                  refine ⟨400936021697052785913241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8553301796203792766149141 400936021697052785913241)
                  ·
                    rfl

theorem cell23_7027381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 6].length) (baseStart_7027381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027381 prefixEnd_7027381 := by exact prefixLift 7027381
  have htrace : WordTrace (prefixWord ++ tailWord_7027381) baseStart_7027381 baseEnd_7027381 := by
    simpa [prefixWord, tailWord_7027381, baseEnd_7027381] using wordTrace_append hprefix tailTrace_7027381
  have hstable : (prefixWord ++ tailWord_7027381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027381).length < 2 ^ (prefixWord ++ tailWord_7027381).sum := by decide
  have hdescent : baseEnd_7027381 < baseStart_7027381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027412 : List Nat := [2, 4, 1, 3, 3, 1, 1, 1, 2, 2, 3]
def baseStart_7027412 : Nat := 118140960795 + 7027412 * 2 ^ 59
def prefixEnd_7027412 : Nat := 4983230072969 + 3 ^ 40 * 7027412 * 2
def baseEnd_7027412 : Nat := 3608440113173764451931527

theorem tailTrace_7027412 : CollatzResearch.WordTrace tailWord_7027412 prefixEnd_7027412 3608440113173764451931527 := by
  unfold tailWord_7027412
  simp only [CollatzResearch.WordTrace]
  refine ⟨128155386208446992631494245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170873848277929323508658993 128155386208446992631494245)
  ·
    refine ⟨24029134914083811118405171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128155386208446992631494245 24029134914083811118405171)
    ·
      refine ⟨36043702371125716677607757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24029134914083811118405171 36043702371125716677607757)
      ·
        refine ⟨13516388389172143754102909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36043702371125716677607757 13516388389172143754102909)
        ·
          refine ⟨5068645645939553907788591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13516388389172143754102909 5068645645939553907788591)
          ·
            refine ⟨7602968468909330861682887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5068645645939553907788591 7602968468909330861682887)
            ·
              refine ⟨11404452703363996292524331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7602968468909330861682887 11404452703363996292524331)
              ·
                refine ⟨17106679055045994438786497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11404452703363996292524331 17106679055045994438786497)
                ·
                  refine ⟨12830009291284495829089873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17106679055045994438786497 12830009291284495829089873)
                  ·
                    refine ⟨9622506968463371871817405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12830009291284495829089873 9622506968463371871817405)
                    ·
                      refine ⟨3608440113173764451931527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9622506968463371871817405 3608440113173764451931527)
                      ·
                        rfl

theorem cell23_7027412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_7027412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027412 prefixEnd_7027412 := by exact prefixLift 7027412
  have htrace : WordTrace (prefixWord ++ tailWord_7027412) baseStart_7027412 baseEnd_7027412 := by
    simpa [prefixWord, tailWord_7027412, baseEnd_7027412] using wordTrace_append hprefix tailTrace_7027412
  have hstable : (prefixWord ++ tailWord_7027412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027412).length < 2 ^ (prefixWord ++ tailWord_7027412).sum := by decide
  have hdescent : baseEnd_7027412 < baseStart_7027412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027425 : List Nat := [1, 2, 3, 1, 4, 1, 1, 5, 1, 1, 3]
def baseStart_7027425 : Nat := 118140960795 + 7027425 * 2 ^ 59
def prefixEnd_7027425 : Nat := 4983230072969 + 3 ^ 40 * 7027425 * 2
def baseEnd_7027425 : Nat := 3608446788422272901068967

theorem tailTrace_7027425 : CollatzResearch.WordTrace tailWord_7027425 prefixEnd_7027425 3608446788422272901068967 := by
  unfold tailWord_7027425
  simp only [CollatzResearch.WordTrace]
  refine ⟨256311246565846888483211729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170874164377231258988807819 256311246565846888483211729)
  ·
    refine ⟨192233434924385166362408797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256311246565846888483211729 192233434924385166362408797)
    ·
      refine ⟨72087538096644437385903299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192233434924385166362408797 72087538096644437385903299)
      ·
        refine ⟨108131307144966656078854949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72087538096644437385903299 108131307144966656078854949)
        ·
          refine ⟨20274620089681248014785303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108131307144966656078854949 20274620089681248014785303)
          ·
            refine ⟨30411930134521872022177955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20274620089681248014785303 30411930134521872022177955)
            ·
              refine ⟨45617895201782808033266933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30411930134521872022177955 45617895201782808033266933)
              ·
                refine ⟨4276677675167138253118775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45617895201782808033266933 4276677675167138253118775)
                ·
                  refine ⟨6415016512750707379678163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4276677675167138253118775 6415016512750707379678163)
                  ·
                    refine ⟨9622524769126061069517245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6415016512750707379678163 9622524769126061069517245)
                    ·
                      refine ⟨3608446788422272901068967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9622524769126061069517245 3608446788422272901068967)
                      ·
                        rfl

theorem cell23_7027425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 1, 1, 3].length) (baseStart_7027425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027425 prefixEnd_7027425 := by exact prefixLift 7027425
  have htrace : WordTrace (prefixWord ++ tailWord_7027425) baseStart_7027425 baseEnd_7027425 := by
    simpa [prefixWord, tailWord_7027425, baseEnd_7027425] using wordTrace_append hprefix tailTrace_7027425
  have hstable : (prefixWord ++ tailWord_7027425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027425).length < 2 ^ (prefixWord ++ tailWord_7027425).sum := by decide
  have hdescent : baseEnd_7027425 < baseStart_7027425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027428 : List Nat := [2, 3, 1, 1, 1, 4, 4, 1, 1, 5]
def baseStart_7027428 : Nat := 118140960795 + 7027428 * 2 ^ 59
def prefixEnd_7027428 : Nat := 4983230072969 + 3 ^ 40 * 7027428 * 2
def baseEnd_7027428 : Nat := 1202816109621412129777151

theorem tailTrace_7027428 : CollatzResearch.WordTrace tailWord_7027428 prefixEnd_7027428 1202816109621412129777151 := by
  unfold tailWord_7027428
  simp only [CollatzResearch.WordTrace]
  refine ⟨128155677992418009997785469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170874237323224013330380625 128155677992418009997785469)
  ·
    refine ⟨48058379247156753749169551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128155677992418009997785469 48058379247156753749169551)
    ·
      refine ⟨72087568870735130623754327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48058379247156753749169551 72087568870735130623754327)
      ·
        refine ⟨108131353306102695935631491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72087568870735130623754327 108131353306102695935631491)
        ·
          refine ⟨162197029959154043903447237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108131353306102695935631491 162197029959154043903447237)
          ·
            refine ⟨30411943117341383231896357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162197029959154043903447237 30411943117341383231896357)
            ·
              refine ⟨5702239334501509355980567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30411943117341383231896357 5702239334501509355980567)
              ·
                refine ⟨8553359001752264033970851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5702239334501509355980567 8553359001752264033970851)
                ·
                  refine ⟨12830038502628396050956277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8553359001752264033970851 12830038502628396050956277)
                  ·
                    refine ⟨1202816109621412129777151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12830038502628396050956277 1202816109621412129777151)
                    ·
                      rfl

theorem cell23_7027428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_7027428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027428 prefixEnd_7027428 := by exact prefixLift 7027428
  have htrace : WordTrace (prefixWord ++ tailWord_7027428) baseStart_7027428 baseEnd_7027428 := by
    simpa [prefixWord, tailWord_7027428, baseEnd_7027428] using wordTrace_append hprefix tailTrace_7027428
  have hstable : (prefixWord ++ tailWord_7027428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027428).length < 2 ^ (prefixWord ++ tailWord_7027428).sum := by decide
  have hdescent : baseEnd_7027428 < baseStart_7027428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027441 : List Nat := [1, 2, 2, 2, 2, 2, 3, 1, 4, 4]
def baseStart_7027441 : Nat := 118140960795 + 7027441 * 2 ^ 59
def prefixEnd_7027441 : Nat := 4983230072969 + 3 ^ 40 * 7027441 * 2
def baseEnd_7027441 : Nat := 1202818334704248279489631

theorem tailTrace_7027441 : CollatzResearch.WordTrace tailWord_7027441 prefixEnd_7027441 1202818334704248279489631 := by
  unfold tailWord_7027441
  simp only [CollatzResearch.WordTrace]
  refine ⟨256311830133788923215794177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170874553422525948810529451 256311830133788923215794177)
  ·
    refine ⟨192233872600341692411845633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256311830133788923215794177 192233872600341692411845633)
    ·
      refine ⟨144175404450256269308884225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192233872600341692411845633 144175404450256269308884225)
      ·
        refine ⟨108131553337692201981663169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144175404450256269308884225 108131553337692201981663169)
        ·
          refine ⟨81098665003269151486247377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108131553337692201981663169 81098665003269151486247377)
          ·
            refine ⟨60823998752451863614685533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81098665003269151486247377 60823998752451863614685533)
            ·
              refine ⟨22808999532169448855507075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60823998752451863614685533 22808999532169448855507075)
              ·
                refine ⟨34213499298254173283260613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22808999532169448855507075 34213499298254173283260613)
                ·
                  refine ⟨6415031118422657490611365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34213499298254173283260613 6415031118422657490611365)
                  ·
                    refine ⟨1202818334704248279489631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6415031118422657490611365 1202818334704248279489631)
                    ·
                      rfl

theorem cell23_7027441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 4].length) (baseStart_7027441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027441 prefixEnd_7027441 := by exact prefixLift 7027441
  have htrace : WordTrace (prefixWord ++ tailWord_7027441) baseStart_7027441 baseEnd_7027441 := by
    simpa [prefixWord, tailWord_7027441, baseEnd_7027441] using wordTrace_append hprefix tailTrace_7027441
  have hstable : (prefixWord ++ tailWord_7027441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027441).length < 2 ^ (prefixWord ++ tailWord_7027441).sum := by decide
  have hdescent : baseEnd_7027441 < baseStart_7027441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027458 : List Nat := [3, 4, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_7027458 : Nat := 118140960795 + 7027458 * 2 ^ 59
def prefixEnd_7027458 : Nat := 4983230072969 + 3 ^ 40 * 7027458 * 2
def baseEnd_7027458 : Nat := 1202821244427957090652105

theorem tailTrace_7027458 : CollatzResearch.WordTrace tailWord_7027458 prefixEnd_7027458 1202821244427957090652105 := by
  unfold tailWord_7027458
  simp only [CollatzResearch.WordTrace]
  refine ⟨64078112543681833779790757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170874966783151556746108685 64078112543681833779790757)
  ·
    refine ⟨12014646101940343833710767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64078112543681833779790757 12014646101940343833710767)
    ·
      refine ⟨18021969152910515750566151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12014646101940343833710767 18021969152910515750566151)
      ·
        refine ⟨27032953729365773625849227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18021969152910515750566151 27032953729365773625849227)
        ·
          refine ⟨40549430594048660438773841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27032953729365773625849227 40549430594048660438773841)
          ·
            refine ⟨30412072945536495329080381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40549430594048660438773841 30412072945536495329080381)
            ·
              refine ⟨11404527354576185748405143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30412072945536495329080381 11404527354576185748405143)
              ·
                refine ⟨17106791031864278622607715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11404527354576185748405143 17106791031864278622607715)
                ·
                  refine ⟨25660186547796417933911573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17106791031864278622607715 25660186547796417933911573)
                  ·
                    refine ⟨1202821244427957090652105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25660186547796417933911573 1202821244427957090652105)
                    ·
                      rfl

theorem cell23_7027458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_7027458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027458 prefixEnd_7027458 := by exact prefixLift 7027458
  have htrace : WordTrace (prefixWord ++ tailWord_7027458) baseStart_7027458 baseEnd_7027458 := by
    simpa [prefixWord, tailWord_7027458, baseEnd_7027458] using wordTrace_append hprefix tailTrace_7027458
  have hstable : (prefixWord ++ tailWord_7027458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027458).length < 2 ^ (prefixWord ++ tailWord_7027458).sum := by decide
  have hdescent : baseEnd_7027458 < baseStart_7027458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027485 : List Nat := [1, 4, 2, 4, 1, 1, 2, 1, 1, 1, 5]
def baseStart_7027485 : Nat := 118140960795 + 7027485 * 2 ^ 59
def prefixEnd_7027485 : Nat := 4983230072969 + 3 ^ 40 * 7027485 * 2
def baseEnd_7027485 : Nat := 3608477597261542666318691

theorem tailTrace_7027485 : CollatzResearch.WordTrace tailWord_7027485 prefixEnd_7027485 3608477597261542666318691 := by
  unfold tailWord_7027485
  simp only [CollatzResearch.WordTrace]
  refine ⟨256313434945629518730395909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170875623297086345820263939 256313434945629518730395909)
  ·
    refine ⟨48058769052305534761949233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256313434945629518730395909 48058769052305534761949233)
    ·
      refine ⟨36044076789229151071461925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48058769052305534761949233 36044076789229151071461925)
      ·
        refine ⟨6758264397980465825899111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36044076789229151071461925 6758264397980465825899111)
        ·
          refine ⟨10137396596970698738848667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6758264397980465825899111 10137396596970698738848667)
          ·
            refine ⟨15206094895456048108273001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10137396596970698738848667 15206094895456048108273001)
            ·
              refine ⟨11404571171592036081204751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15206094895456048108273001 11404571171592036081204751)
              ·
                refine ⟨17106856757388054121807127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11404571171592036081204751 17106856757388054121807127)
                ·
                  refine ⟨25660285136082081182710691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17106856757388054121807127 25660285136082081182710691)
                  ·
                    refine ⟨38490427704123121774066037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25660285136082081182710691 38490427704123121774066037)
                    ·
                      refine ⟨3608477597261542666318691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38490427704123121774066037 3608477597261542666318691)
                      ·
                        rfl

theorem cell23_7027485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_7027485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027485 prefixEnd_7027485 := by exact prefixLift 7027485
  have htrace : WordTrace (prefixWord ++ tailWord_7027485) baseStart_7027485 baseEnd_7027485 := by
    simpa [prefixWord, tailWord_7027485, baseEnd_7027485] using wordTrace_append hprefix tailTrace_7027485
  have hstable : (prefixWord ++ tailWord_7027485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027485).length < 2 ^ (prefixWord ++ tailWord_7027485).sum := by decide
  have hdescent : baseEnd_7027485 < baseStart_7027485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027541 : List Nat := [1, 3, 2, 2, 2, 1, 1, 3, 2, 1, 5]
def baseStart_7027541 : Nat := 118140960795 + 7027541 * 2 ^ 59
def prefixEnd_7027541 : Nat := 4983230072969 + 3 ^ 40 * 7027541 * 2
def baseEnd_7027541 : Nat := 3608506352178194447218433

theorem tailTrace_7027541 : CollatzResearch.WordTrace tailWord_7027541 prefixEnd_7027541 3608506352178194447218433 := by
  unfold tailWord_7027541
  simp only [CollatzResearch.WordTrace]
  refine ⟨256315477433426640294434477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170876984955617760196289651 256315477433426640294434477)
  ·
    refine ⟨96118304037534990110412929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256315477433426640294434477 96118304037534990110412929)
    ·
      refine ⟨72088728028151242582809697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96118304037534990110412929 72088728028151242582809697)
      ·
        refine ⟨54066546021113431937107273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72088728028151242582809697 54066546021113431937107273)
        ·
          refine ⟨40549909515835073952830455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54066546021113431937107273 40549909515835073952830455)
          ·
            refine ⟨60824864273752610929245683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40549909515835073952830455 60824864273752610929245683)
            ·
              refine ⟨91237296410628916393868525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60824864273752610929245683 91237296410628916393868525)
              ·
                refine ⟨34213986153985843647700697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91237296410628916393868525 34213986153985843647700697)
                ·
                  refine ⟨25660489615489382735775523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34213986153985843647700697 25660489615489382735775523)
                  ·
                    refine ⟨38490734423234074103663285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25660489615489382735775523 38490734423234074103663285)
                    ·
                      refine ⟨3608506352178194447218433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38490734423234074103663285 3608506352178194447218433)
                      ·
                        rfl

theorem cell23_7027541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_7027541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027541 prefixEnd_7027541 := by exact prefixLift 7027541
  have htrace : WordTrace (prefixWord ++ tailWord_7027541) baseStart_7027541 baseEnd_7027541 := by
    simpa [prefixWord, tailWord_7027541, baseEnd_7027541] using wordTrace_append hprefix tailTrace_7027541
  have hstable : (prefixWord ++ tailWord_7027541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027541).length < 2 ^ (prefixWord ++ tailWord_7027541).sum := by decide
  have hdescent : baseEnd_7027541 < baseStart_7027541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027551 : List Nat := [1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 4]
def baseStart_7027551 : Nat := 118140960795 + 7027551 * 2 ^ 59
def prefixEnd_7027551 : Nat := 4983230072969 + 3 ^ 40 * 7027551 * 2
def baseEnd_7027551 : Nat := 3608511486984739408093387

theorem tailTrace_7027551 : CollatzResearch.WordTrace tailWord_7027551 prefixEnd_7027551 3608511486984739408093387 := by
  unfold tailWord_7027551
  simp only [CollatzResearch.WordTrace]
  refine ⟨256315842163390412002298507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170877228108926941334865671 256315842163390412002298507)
  ·
    refine ⟨384473763245085618003447761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256315842163390412002298507 384473763245085618003447761)
    ·
      refine ⟨288355322433814213502585821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384473763245085618003447761 288355322433814213502585821)
      ·
        refine ⟨108133245912680330063469683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288355322433814213502585821 108133245912680330063469683)
        ·
          refine ⟨162199868869020495095204525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108133245912680330063469683 162199868869020495095204525)
          ·
            refine ⟨60824950825882685660701697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162199868869020495095204525 60824950825882685660701697)
            ·
              refine ⟨45618713119412014245526273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60824950825882685660701697 45618713119412014245526273)
              ·
                refine ⟨34214034839559010684144705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45618713119412014245526273 34214034839559010684144705)
                ·
                  refine ⟨25660526129669258013108529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34214034839559010684144705 25660526129669258013108529)
                  ·
                    refine ⟨19245394597251943509831397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25660526129669258013108529 19245394597251943509831397)
                    ·
                      refine ⟨3608511486984739408093387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19245394597251943509831397 3608511486984739408093387)
                      ·
                        rfl

theorem cell23_7027551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_7027551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027551 prefixEnd_7027551 := by exact prefixLift 7027551
  have htrace : WordTrace (prefixWord ++ tailWord_7027551) baseStart_7027551 baseEnd_7027551 := by
    simpa [prefixWord, tailWord_7027551, baseEnd_7027551] using wordTrace_append hprefix tailTrace_7027551
  have hstable : (prefixWord ++ tailWord_7027551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027551).length < 2 ^ (prefixWord ++ tailWord_7027551).sum := by decide
  have hdescent : baseEnd_7027551 < baseStart_7027551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027571 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 3]
def baseStart_7027571 : Nat := 118140960795 + 7027571 * 2 ^ 59
def prefixEnd_7027571 : Nat := 4983230072969 + 3 ^ 40 * 7027571 * 2
def baseEnd_7027571 : Nat := 3608521756597829329843295

theorem tailTrace_7027571 : CollatzResearch.WordTrace tailWord_7027571 prefixEnd_7027571 3608521756597829329843295 := by
  unfold tailWord_7027571
  simp only [CollatzResearch.WordTrace]
  refine ⟨256316571623317955418026567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170877714415545303612017711 256316571623317955418026567)
  ·
    refine ⟨384474857434976933127039851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256316571623317955418026567 384474857434976933127039851)
    ·
      refine ⟨576712286152465399690559777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384474857434976933127039851 576712286152465399690559777)
      ·
        refine ⟨432534214614349049767919833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 576712286152465399690559777 432534214614349049767919833)
        ·
          refine ⟨324400660960761787325939875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 432534214614349049767919833 324400660960761787325939875)
          ·
            refine ⟨486600991441142680988909813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324400660960761787325939875 486600991441142680988909813)
            ·
              refine ⟨45618842947607126342710295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 486600991441142680988909813 45618842947607126342710295)
              ·
                refine ⟨68428264421410689514065443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45618842947607126342710295 68428264421410689514065443)
                ·
                  refine ⟨102642396632116034271098165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68428264421410689514065443 102642396632116034271098165)
                  ·
                    refine ⟨9622724684260878212915453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102642396632116034271098165 9622724684260878212915453)
                    ·
                      refine ⟨3608521756597829329843295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9622724684260878212915453 3608521756597829329843295)
                      ·
                        rfl

theorem cell23_7027571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 3].length) (baseStart_7027571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027571 prefixEnd_7027571 := by exact prefixLift 7027571
  have htrace : WordTrace (prefixWord ++ tailWord_7027571) baseStart_7027571 baseEnd_7027571 := by
    simpa [prefixWord, tailWord_7027571, baseEnd_7027571] using wordTrace_append hprefix tailTrace_7027571
  have hstable : (prefixWord ++ tailWord_7027571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027571).length < 2 ^ (prefixWord ++ tailWord_7027571).sum := by decide
  have hdescent : baseEnd_7027571 < baseStart_7027571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027606 : List Nat := [5, 3, 1, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_7027606 : Nat := 118140960795 + 7027606 * 2 ^ 59
def prefixEnd_7027606 : Nat := 4983230072969 + 3 ^ 40 * 7027606 * 2
def baseEnd_7027606 : Nat := 3608539728420736692905635

theorem tailTrace_7027606 : CollatzResearch.WordTrace tailWord_7027606 prefixEnd_7027606 3608539728420736692905635 := by
  unfold tailWord_7027606
  simp only [CollatzResearch.WordTrace]
  refine ⟨16019865511136947274721917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170878565452127437597033781 16019865511136947274721917)
  ·
    refine ⟨6007449566676355228020719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16019865511136947274721917 6007449566676355228020719)
    ·
      refine ⟨9011174350014532842031079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6007449566676355228020719 9011174350014532842031079)
      ·
        refine ⟨13516761525021799263046619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9011174350014532842031079 13516761525021799263046619)
        ·
          refine ⟨20275142287532698894569929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13516761525021799263046619 20275142287532698894569929)
          ·
            refine ⟨15206356715649524170927447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20275142287532698894569929 15206356715649524170927447)
            ·
              refine ⟨22809535073474286256391171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15206356715649524170927447 22809535073474286256391171)
              ·
                refine ⟨34214302610211429384586757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22809535073474286256391171 34214302610211429384586757)
                ·
                  refine ⟨6415181739414643009610017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34214302610211429384586757 6415181739414643009610017)
                  ·
                    refine ⟨4811386304560982257207513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6415181739414643009610017 4811386304560982257207513)
                    ·
                      refine ⟨3608539728420736692905635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4811386304560982257207513 3608539728420736692905635)
                      ·
                        rfl

theorem cell23_7027606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_7027606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027606 prefixEnd_7027606 := by exact prefixLift 7027606
  have htrace : WordTrace (prefixWord ++ tailWord_7027606) baseStart_7027606 baseEnd_7027606 := by
    simpa [prefixWord, tailWord_7027606, baseEnd_7027606] using wordTrace_append hprefix tailTrace_7027606
  have hstable : (prefixWord ++ tailWord_7027606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027606).length < 2 ^ (prefixWord ++ tailWord_7027606).sum := by decide
  have hdescent : baseEnd_7027606 < baseStart_7027606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027648 : List Nat := [2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 3]
def baseStart_7027648 : Nat := 118140960795 + 7027648 * 2 ^ 59
def prefixEnd_7027648 : Nat := 4983230072969 + 3 ^ 40 * 7027648 * 2
def baseEnd_7027648 : Nat := 3608561294608225528580441

theorem tailTrace_7027648 : CollatzResearch.WordTrace tailWord_7027648 prefixEnd_7027648 3608561294608225528580441 := by
  unfold tailWord_7027648
  simp only [CollatzResearch.WordTrace]
  refine ⟨128159690022019498784289799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170879586696025998379053065 128159690022019498784289799)
  ·
    refine ⟨192239535033029248176434699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128159690022019498784289799 192239535033029248176434699)
    ·
      refine ⟨288359302549543872264652049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192239535033029248176434699 288359302549543872264652049)
      ·
        refine ⟨216269476912157904198489037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288359302549543872264652049 216269476912157904198489037)
        ·
          refine ⟨81101053842059214074433389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216269476912157904198489037 81101053842059214074433389)
          ·
            refine ⟨30412895190772205277912521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81101053842059214074433389 30412895190772205277912521)
            ·
              refine ⟨22809671393079153958434391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30412895190772205277912521 22809671393079153958434391)
              ·
                refine ⟨34214507089618730937651587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22809671393079153958434391 34214507089618730937651587)
                ·
                  refine ⟨51321760634428096406477381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34214507089618730937651587 51321760634428096406477381)
                  ·
                    refine ⟨9622830118955268076214509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51321760634428096406477381 9622830118955268076214509)
                    ·
                      refine ⟨3608561294608225528580441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9622830118955268076214509 3608561294608225528580441)
                      ·
                        rfl

theorem cell23_7027648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 3].length) (baseStart_7027648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027648 prefixEnd_7027648 := by exact prefixLift 7027648
  have htrace : WordTrace (prefixWord ++ tailWord_7027648) baseStart_7027648 baseEnd_7027648 := by
    simpa [prefixWord, tailWord_7027648, baseEnd_7027648] using wordTrace_append hprefix tailTrace_7027648
  have hstable : (prefixWord ++ tailWord_7027648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027648).length < 2 ^ (prefixWord ++ tailWord_7027648).sum := by decide
  have hdescent : baseEnd_7027648 < baseStart_7027648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027668 : List Nat := [2, 4, 1, 2, 1, 2, 2, 1, 8]
def baseStart_7027668 : Nat := 118140960795 + 7027668 * 2 ^ 59
def prefixEnd_7027668 : Nat := 4983230072969 + 3 ^ 40 * 7027668 * 2
def baseEnd_7027668 : Nat := 400952396024590605592261

theorem tailTrace_7027668 : CollatzResearch.WordTrace tailWord_7027668 prefixEnd_7027668 400952396024590605592261 := by
  unfold tailWord_7027668
  simp only [CollatzResearch.WordTrace]
  refine ⟨128160054751983270492153829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170880073002644360656205105 128160054751983270492153829)
  ·
    refine ⟨24030010265996863217278843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128160054751983270492153829 24030010265996863217278843)
    ·
      refine ⟨36045015398995294825918265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24030010265996863217278843 36045015398995294825918265)
      ·
        refine ⟨27033761549246471119438699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36045015398995294825918265 27033761549246471119438699)
        ·
          refine ⟨40550642323869706679158049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27033761549246471119438699 40550642323869706679158049)
          ·
            refine ⟨30412981742902280009368537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40550642323869706679158049 30412981742902280009368537)
            ·
              refine ⟨22809736307176710007026403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30412981742902280009368537 22809736307176710007026403)
              ·
                refine ⟨34214604460765065010539605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22809736307176710007026403 34214604460765065010539605)
                ·
                  refine ⟨400952396024590605592261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34214604460765065010539605 400952396024590605592261)
                  ·
                    rfl

theorem cell23_7027668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_7027668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027668 prefixEnd_7027668 := by exact prefixLift 7027668
  have htrace : WordTrace (prefixWord ++ tailWord_7027668) baseStart_7027668 baseEnd_7027668 := by
    simpa [prefixWord, tailWord_7027668, baseEnd_7027668] using wordTrace_append hprefix tailTrace_7027668
  have hstable : (prefixWord ++ tailWord_7027668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027668).length < 2 ^ (prefixWord ++ tailWord_7027668).sum := by decide
  have hdescent : baseEnd_7027668 < baseStart_7027668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027671 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 6]
def baseStart_7027671 : Nat := 118140960795 + 7027671 * 2 ^ 59
def prefixEnd_7027671 : Nat := 4983230072969 + 3 ^ 40 * 7027671 * 2
def baseEnd_7027671 : Nat := 3608573104663278938592835

theorem tailTrace_7027671 : CollatzResearch.WordTrace tailWord_7027671 prefixEnd_7027671 3608573104663278938592835 := by
  unfold tailWord_7027671
  simp only [CollatzResearch.WordTrace]
  refine ⟨256320218922955672496666867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170880145948637114997777911 256320218922955672496666867)
  ·
    refine ⟨384480328384433508745000301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256320218922955672496666867 384480328384433508745000301)
    ·
      refine ⟨144180123144162565779375113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384480328384433508745000301 144180123144162565779375113)
      ·
        refine ⟨108135092358121924334531335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144180123144162565779375113 108135092358121924334531335)
        ·
          refine ⟨162202638537182886501797003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108135092358121924334531335 162202638537182886501797003)
          ·
            refine ⟨243303957805774329752695505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162202638537182886501797003 243303957805774329752695505)
            ·
              refine ⟨182477968354330747314521629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243303957805774329752695505 182477968354330747314521629)
              ·
                refine ⟨68429238132874030242945611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182477968354330747314521629 68429238132874030242945611)
                ·
                  refine ⟨102643857199311045364418417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68429238132874030242945611 102643857199311045364418417)
                  ·
                    refine ⟨76982892899483284023313813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102643857199311045364418417 76982892899483284023313813)
                    ·
                      refine ⟨3608573104663278938592835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76982892899483284023313813 3608573104663278938592835)
                      ·
                        rfl

theorem cell23_7027671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_7027671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027671 prefixEnd_7027671 := by exact prefixLift 7027671
  have htrace : WordTrace (prefixWord ++ tailWord_7027671) baseStart_7027671 baseEnd_7027671 := by
    simpa [prefixWord, tailWord_7027671, baseEnd_7027671] using wordTrace_append hprefix tailTrace_7027671
  have hstable : (prefixWord ++ tailWord_7027671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027671).length < 2 ^ (prefixWord ++ tailWord_7027671).sum := by decide
  have hdescent : baseEnd_7027671 < baseStart_7027671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027681 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 2, 9]
def baseStart_7027681 : Nat := 118140960795 + 7027681 * 2 ^ 59
def prefixEnd_7027681 : Nat := 4983230072969 + 3 ^ 40 * 7027681 * 2
def baseEnd_7027681 : Nat := 1202859413156607966489263

theorem tailTrace_7027681 : CollatzResearch.WordTrace tailWord_7027681 prefixEnd_7027681 1202859413156607966489263 := by
  unfold tailWord_7027681
  simp only [CollatzResearch.WordTrace]
  refine ⟨256320583652919444204530897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170880389101946296136353931 256320583652919444204530897)
  ·
    refine ⟨192240437739689583153398173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256320583652919444204530897 192240437739689583153398173)
    ·
      refine ⟨72090164152383593682524315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192240437739689583153398173 72090164152383593682524315)
      ·
        refine ⟨108135246228575390523786473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72090164152383593682524315 108135246228575390523786473)
        ·
          refine ⟨81101434671431542892839855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108135246228575390523786473 81101434671431542892839855)
          ·
            refine ⟨121652152007147314339259783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81101434671431542892839855 121652152007147314339259783)
            ·
              refine ⟨182478228010720971508889675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121652152007147314339259783 182478228010720971508889675)
              ·
                refine ⟨273717342016081457263334513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182478228010720971508889675 273717342016081457263334513)
                ·
                  refine ⟨205288006512061092947500885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273717342016081457263334513 205288006512061092947500885)
                  ·
                    refine ⟨1202859413156607966489263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 205288006512061092947500885 1202859413156607966489263)
                    ·
                      rfl

theorem cell23_7027681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_7027681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027681 prefixEnd_7027681 := by exact prefixLift 7027681
  have htrace : WordTrace (prefixWord ++ tailWord_7027681) baseStart_7027681 baseEnd_7027681 := by
    simpa [prefixWord, tailWord_7027681, baseEnd_7027681] using wordTrace_append hprefix tailTrace_7027681
  have hstable : (prefixWord ++ tailWord_7027681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027681).length < 2 ^ (prefixWord ++ tailWord_7027681).sum := by decide
  have hdescent : baseEnd_7027681 < baseStart_7027681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027722 : List Nat := [3, 1, 2, 2, 3, 1, 2, 2, 2, 3, 2]
def baseStart_7027722 : Nat := 118140960795 + 7027722 * 2 ^ 59
def prefixEnd_7027722 : Nat := 4983230072969 + 3 ^ 40 * 7027722 * 2
def baseEnd_7027722 : Nat := 3608599292176658239055101

theorem tailTrace_7027722 : CollatzResearch.WordTrace tailWord_7027722 prefixEnd_7027722 3608599292176658239055101 := by
  unfold tailWord_7027722
  simp only [CollatzResearch.WordTrace]
  refine ⟨64080519761442727051693355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170881386030513938804515613 64080519761442727051693355)
  ·
    refine ⟨96120779642164090577540033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64080519761442727051693355 96120779642164090577540033)
    ·
      refine ⟨72090584731623067933155025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96120779642164090577540033 72090584731623067933155025)
      ·
        refine ⟨54067938548717300949866269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72090584731623067933155025 54067938548717300949866269)
        ·
          refine ⟨20275476955768987856199851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54067938548717300949866269 20275476955768987856199851)
          ·
            refine ⟨30413215433653481784299777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20275476955768987856199851 30413215433653481784299777)
            ·
              refine ⟨22809911575240111338224833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30413215433653481784299777 22809911575240111338224833)
              ·
                refine ⟨17107433681430083503668625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22809911575240111338224833 17107433681430083503668625)
                ·
                  refine ⟨12830575261072562627751469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17107433681430083503668625 12830575261072562627751469)
                  ·
                    refine ⟨4811465722902210985406801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12830575261072562627751469 4811465722902210985406801)
                    ·
                      refine ⟨3608599292176658239055101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4811465722902210985406801 3608599292176658239055101)
                      ·
                        rfl

theorem cell23_7027722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_7027722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027722 prefixEnd_7027722 := by exact prefixLift 7027722
  have htrace : WordTrace (prefixWord ++ tailWord_7027722) baseStart_7027722 baseEnd_7027722 := by
    simpa [prefixWord, tailWord_7027722, baseEnd_7027722] using wordTrace_append hprefix tailTrace_7027722
  have hstable : (prefixWord ++ tailWord_7027722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027722).length < 2 ^ (prefixWord ++ tailWord_7027722).sum := by decide
  have hdescent : baseEnd_7027722 < baseStart_7027722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027735 : List Nat := [1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 4]
def baseStart_7027735 : Nat := 118140960795 + 7027735 * 2 ^ 59
def prefixEnd_7027735 : Nat := 4983230072969 + 3 ^ 40 * 7027735 * 2
def baseEnd_7027735 : Nat := 3608605967425166688192541

theorem tailTrace_7027735 : CollatzResearch.WordTrace tailWord_7027735 prefixEnd_7027735 3608605967425166688192541 := by
  unfold tailWord_7027735
  simp only [CollatzResearch.WordTrace]
  refine ⟨256322553194723811426996659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170881702129815874284664439 256322553194723811426996659)
  ·
    refine ⟨384483829792085717140494989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256322553194723811426996659 384483829792085717140494989)
    ·
      refine ⟨144181436172032143927685621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384483829792085717140494989 144181436172032143927685621)
      ·
        refine ⟨13517009641128013493220527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144181436172032143927685621 13517009641128013493220527)
        ·
          refine ⟨20275514461692020239830791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13517009641128013493220527 20275514461692020239830791)
          ·
            refine ⟨30413271692538030359746187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20275514461692020239830791 30413271692538030359746187)
            ·
              refine ⟨45619907538807045539619281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30413271692538030359746187 45619907538807045539619281)
              ·
                refine ⟨34214930654105284154714461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45619907538807045539619281 34214930654105284154714461)
                ·
                  refine ⟨12830598995289481558017923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34214930654105284154714461 12830598995289481558017923)
                  ·
                    refine ⟨19245898492934222337026885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12830598995289481558017923 19245898492934222337026885)
                    ·
                      refine ⟨3608605967425166688192541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19245898492934222337026885 3608605967425166688192541)
                      ·
                        rfl

theorem cell23_7027735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_7027735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027735 prefixEnd_7027735 := by exact prefixLift 7027735
  have htrace : WordTrace (prefixWord ++ tailWord_7027735) baseStart_7027735 baseEnd_7027735 := by
    simpa [prefixWord, tailWord_7027735, baseEnd_7027735] using wordTrace_append hprefix tailTrace_7027735
  have hstable : (prefixWord ++ tailWord_7027735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027735).length < 2 ^ (prefixWord ++ tailWord_7027735).sum := by decide
  have hdescent : baseEnd_7027735 < baseStart_7027735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027738 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5]
def baseStart_7027738 : Nat := 118140960795 + 7027738 * 2 ^ 59
def prefixEnd_7027738 : Nat := 4983230072969 + 3 ^ 40 * 7027738 * 2
def baseEnd_7027738 : Nat := 3608607507867130176455027

theorem tailTrace_7027738 : CollatzResearch.WordTrace tailWord_7027738 prefixEnd_7027738 3608607507867130176455027 := by
  unfold tailWord_7027738
  simp only [CollatzResearch.WordTrace]
  refine ⟨64080665653428235734838967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170881775075808628626237245 64080665653428235734838967)
  ·
    refine ⟨96120998480142353602258451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64080665653428235734838967 96120998480142353602258451)
    ·
      refine ⟨144181497720213530403387677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96120998480142353602258451 144181497720213530403387677)
      ·
        refine ⟨54068061645080073901270379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144181497720213530403387677 54068061645080073901270379)
        ·
          refine ⟨81102092467620110851905569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54068061645080073901270379 81102092467620110851905569)
          ·
            refine ⟨60826569350715083138929177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81102092467620110851905569 60826569350715083138929177)
            ·
              refine ⟨45619927013036312354196883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60826569350715083138929177 45619927013036312354196883)
              ·
                refine ⟨68429890519554468531295325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45619927013036312354196883 68429890519554468531295325)
                ·
                  refine ⟨25661208944832925699235747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68429890519554468531295325 25661208944832925699235747)
                  ·
                    refine ⟨38491813417249388548853621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25661208944832925699235747 38491813417249388548853621)
                    ·
                      refine ⟨3608607507867130176455027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38491813417249388548853621 3608607507867130176455027)
                      ·
                        rfl

theorem cell23_7027738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_7027738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027738 prefixEnd_7027738 := by exact prefixLift 7027738
  have htrace : WordTrace (prefixWord ++ tailWord_7027738) baseStart_7027738 baseEnd_7027738 := by
    simpa [prefixWord, tailWord_7027738, baseEnd_7027738] using wordTrace_append hprefix tailTrace_7027738
  have hstable : (prefixWord ++ tailWord_7027738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027738).length < 2 ^ (prefixWord ++ tailWord_7027738).sum := by decide
  have hdescent : baseEnd_7027738 < baseStart_7027738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027745 : List Nat := [1, 2, 3, 2, 3, 2, 2, 1, 1, 6]
def baseStart_7027745 : Nat := 118140960795 + 7027745 * 2 ^ 59
def prefixEnd_7027745 : Nat := 4983230072969 + 3 ^ 40 * 7027745 * 2
def baseEnd_7027745 : Nat := 1202870367410570549689165

theorem tailTrace_7027745 : CollatzResearch.WordTrace tailWord_7027745 prefixEnd_7027745 1202870367410570549689165 := by
  unfold tailWord_7027745
  simp only [CollatzResearch.WordTrace]
  refine ⟨256322917924687583134860689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170881945283125055423240459 256322917924687583134860689)
  ·
    refine ⟨192242188443515687351145517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256322917924687583134860689 192242188443515687351145517)
    ·
      refine ⟨72090820666318382756679569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192242188443515687351145517 72090820666318382756679569)
      ·
        refine ⟨54068115499738787067509677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72090820666318382756679569 54068115499738787067509677)
        ·
          refine ⟨20275543312402045150316129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54068115499738787067509677 20275543312402045150316129)
          ·
            refine ⟨15206657484301533862737097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20275543312402045150316129 15206657484301533862737097)
            ·
              refine ⟨11404993113226150397052823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15206657484301533862737097 11404993113226150397052823)
              ·
                refine ⟨17107489669839225595579235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11404993113226150397052823 17107489669839225595579235)
                ·
                  refine ⟨25661234504758838393368853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17107489669839225595579235 25661234504758838393368853)
                  ·
                    refine ⟨1202870367410570549689165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25661234504758838393368853 1202870367410570549689165)
                    ·
                      rfl

theorem cell23_7027745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_7027745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027745 prefixEnd_7027745 := by exact prefixLift 7027745
  have htrace : WordTrace (prefixWord ++ tailWord_7027745) baseStart_7027745 baseEnd_7027745 := by
    simpa [prefixWord, tailWord_7027745, baseEnd_7027745] using wordTrace_append hprefix tailTrace_7027745
  have hstable : (prefixWord ++ tailWord_7027745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027745).length < 2 ^ (prefixWord ++ tailWord_7027745).sum := by decide
  have hdescent : baseEnd_7027745 < baseStart_7027745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027755 : List Nat := [1, 1, 1, 1, 2, 1, 6, 4, 1, 2, 3]
def baseStart_7027755 : Nat := 118140960795 + 7027755 * 2 ^ 59
def prefixEnd_7027755 : Nat := 4983230072969 + 3 ^ 40 * 7027755 * 2
def baseEnd_7027755 : Nat := 3608616237038256609942449

theorem tailTrace_7027755 : CollatzResearch.WordTrace tailWord_7027755 prefixEnd_7027755 3608616237038256609942449 := by
  unfold tailWord_7027755
  simp only [CollatzResearch.WordTrace]
  refine ⟨256323282654651354842724719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170882188436434236561816479 256323282654651354842724719)
  ·
    refine ⟨384484923981977032264087079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256323282654651354842724719 384484923981977032264087079)
    ·
      refine ⟨576727385972965548396130619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384484923981977032264087079 576727385972965548396130619)
      ·
        refine ⟨865091078959448322594195929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576727385972965548396130619 865091078959448322594195929)
        ·
          refine ⟨648818309219586241945646947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 865091078959448322594195929 648818309219586241945646947)
          ·
            refine ⟨973227463829379362918470421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648818309219586241945646947 973227463829379362918470421)
            ·
              refine ⟨45620037367002157636803301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 973227463829379362918470421 45620037367002157636803301)
              ·
                refine ⟨8553757006312904556900619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45620037367002157636803301 8553757006312904556900619)
                ·
                  refine ⟨12830635509469356835350929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8553757006312904556900619 12830635509469356835350929)
                  ·
                    refine ⟨9622976632102017626513197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12830635509469356835350929 9622976632102017626513197)
                    ·
                      refine ⟨3608616237038256609942449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9622976632102017626513197 3608616237038256609942449)
                      ·
                        rfl

theorem cell23_7027755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 2, 3].length) (baseStart_7027755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027755 prefixEnd_7027755 := by exact prefixLift 7027755
  have htrace : WordTrace (prefixWord ++ tailWord_7027755) baseStart_7027755 baseEnd_7027755 := by
    simpa [prefixWord, tailWord_7027755, baseEnd_7027755] using wordTrace_append hprefix tailTrace_7027755
  have hstable : (prefixWord ++ tailWord_7027755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027755).length < 2 ^ (prefixWord ++ tailWord_7027755).sum := by decide
  have hdescent : baseEnd_7027755 < baseStart_7027755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027769 : List Nat := [1, 2, 1, 5, 2, 3, 2, 1, 1, 1, 4]
def baseStart_7027769 : Nat := 118140960795 + 7027769 * 2 ^ 59
def prefixEnd_7027769 : Nat := 4983230072969 + 3 ^ 40 * 7027769 * 2
def baseEnd_7027769 : Nat := 3608623425767419555167385

theorem tailTrace_7027769 : CollatzResearch.WordTrace tailWord_7027769 prefixEnd_7027769 3608623425767419555167385 := by
  unfold tailWord_7027769
  simp only [CollatzResearch.WordTrace]
  refine ⟨256323793276600635233734361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170882528851067090155822907 256323793276600635233734361)
  ·
    refine ⟨192242844957450476425300771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256323793276600635233734361 192242844957450476425300771)
    ·
      refine ⟨288364267436175714637951157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192242844957450476425300771 288364267436175714637951157)
      ·
        refine ⟨27034150072141473247307921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 288364267436175714637951157 27034150072141473247307921)
        ·
          refine ⟨20275612554106104935480941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27034150072141473247307921 20275612554106104935480941)
          ·
            refine ⟨7603354707789789350805353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20275612554106104935480941 7603354707789789350805353)
            ·
              refine ⟨5702516030842342013104015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7603354707789789350805353 5702516030842342013104015)
              ·
                refine ⟨8553774046263513019656023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5702516030842342013104015 8553774046263513019656023)
                ·
                  refine ⟨12830661069395269529484035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8553774046263513019656023 12830661069395269529484035)
                  ·
                    refine ⟨19245991604092904294226053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12830661069395269529484035 19245991604092904294226053)
                    ·
                      refine ⟨3608623425767419555167385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19245991604092904294226053 3608623425767419555167385)
                      ·
                        rfl

theorem cell23_7027769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_7027769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027769 prefixEnd_7027769 := by exact prefixLift 7027769
  have htrace : WordTrace (prefixWord ++ tailWord_7027769) baseStart_7027769 baseEnd_7027769 := by
    simpa [prefixWord, tailWord_7027769, baseEnd_7027769] using wordTrace_append hprefix tailTrace_7027769
  have hstable : (prefixWord ++ tailWord_7027769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027769).length < 2 ^ (prefixWord ++ tailWord_7027769).sum := by decide
  have hdescent : baseEnd_7027769 < baseStart_7027769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027772 : List Nat := [2, 2, 2, 2, 2, 3, 1, 3, 1, 2, 3]
def baseStart_7027772 : Nat := 118140960795 + 7027772 * 2 ^ 59
def prefixEnd_7027772 : Nat := 4983230072969 + 3 ^ 40 * 7027772 * 2
def baseEnd_7027772 : Nat := 3608624966209383043429871

theorem tailTrace_7027772 : CollatzResearch.WordTrace tailWord_7027772 prefixEnd_7027772 3608624966209383043429871 := by
  unfold tailWord_7027772
  simp only [CollatzResearch.WordTrace]
  refine ⟨128161951347794883373046785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170882601797059844497395713 128161951347794883373046785)
  ·
    refine ⟨96121463510846162529785089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128161951347794883373046785 96121463510846162529785089)
    ·
      refine ⟨72091097633134621897338817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96121463510846162529785089 72091097633134621897338817)
      ·
        refine ⟨54068323224850966423004113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72091097633134621897338817 54068323224850966423004113)
        ·
          refine ⟨40551242418638224817253085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54068323224850966423004113 40551242418638224817253085)
          ·
            refine ⟨15206715906989334306469907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40551242418638224817253085 15206715906989334306469907)
            ·
              refine ⟨22810073860484001459704861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15206715906989334306469907 22810073860484001459704861)
              ·
                refine ⟨8553777697681500547389323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22810073860484001459704861 8553777697681500547389323)
                ·
                  refine ⟨12830666546522250821083985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8553777697681500547389323 12830666546522250821083985)
                  ·
                    refine ⟨9622999909891688115812989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12830666546522250821083985 9622999909891688115812989)
                    ·
                      refine ⟨3608624966209383043429871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9622999909891688115812989 3608624966209383043429871)
                      ·
                        rfl

theorem cell23_7027772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_7027772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027772 prefixEnd_7027772 := by exact prefixLift 7027772
  have htrace : WordTrace (prefixWord ++ tailWord_7027772) baseStart_7027772 baseEnd_7027772 := by
    simpa [prefixWord, tailWord_7027772, baseEnd_7027772] using wordTrace_append hprefix tailTrace_7027772
  have hstable : (prefixWord ++ tailWord_7027772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027772).length < 2 ^ (prefixWord ++ tailWord_7027772).sum := by decide
  have hdescent : baseEnd_7027772 < baseStart_7027772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027806 : List Nat := [4, 4, 1, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_7027806 : Nat := 118140960795 + 7027806 * 2 ^ 59
def prefixEnd_7027806 : Nat := 4983230072969 + 3 ^ 40 * 7027806 * 2
def baseEnd_7027806 : Nat := 3608642424551635910404715

theorem tailTrace_7027806 : CollatzResearch.WordTrace tailWord_7027806 prefixEnd_7027806 3608642424551635910404715 := by
  unfold tailWord_7027806
  simp only [CollatzResearch.WordTrace]
  refine ⟨32040642847183323819103909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170883428518311060368554181 32040642847183323819103909)
  ·
    refine ⟨6007620533846873216081983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32040642847183323819103909 6007620533846873216081983)
    ·
      refine ⟨9011430800770309824122975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6007620533846873216081983 9011430800770309824122975)
      ·
        refine ⟨13517146201155464736184463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9011430800770309824122975 13517146201155464736184463)
        ·
          refine ⟨20275719301733197104276695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13517146201155464736184463 20275719301733197104276695)
          ·
            refine ⟨30413578952599795656415043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20275719301733197104276695 30413578952599795656415043)
            ·
              refine ⟨45620368428899693484622565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30413578952599795656415043 45620368428899693484622565)
              ·
                refine ⟨8553819080418692528366731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45620368428899693484622565 8553819080418692528366731)
                ·
                  refine ⟨12830728620628038792550097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8553819080418692528366731 12830728620628038792550097)
                  ·
                    refine ⟨9623046465471029094412573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12830728620628038792550097 9623046465471029094412573)
                    ·
                      refine ⟨3608642424551635910404715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9623046465471029094412573 3608642424551635910404715)
                      ·
                        rfl

theorem cell23_7027806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_7027806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027806 prefixEnd_7027806 := by exact prefixLift 7027806
  have htrace : WordTrace (prefixWord ++ tailWord_7027806) baseStart_7027806 baseEnd_7027806 := by
    simpa [prefixWord, tailWord_7027806, baseEnd_7027806] using wordTrace_append hprefix tailTrace_7027806
  have hstable : (prefixWord ++ tailWord_7027806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027806).length < 2 ^ (prefixWord ++ tailWord_7027806).sum := by decide
  have hdescent : baseEnd_7027806 < baseStart_7027806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027888 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 7]
def baseStart_7027888 : Nat := 118140960795 + 7027888 * 2 ^ 59
def prefixEnd_7027888 : Nat := 4983230072969 + 3 ^ 40 * 7027888 * 2
def baseEnd_7027888 : Nat := 3608684529965304589579337

theorem tailTrace_7027888 : CollatzResearch.WordTrace tailWord_7027888 prefixEnd_7027888 3608684529965304589579337 := by
  unfold tailWord_7027888
  simp only [CollatzResearch.WordTrace]
  refine ⟨128164066781584759278658159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170885422375446345704877545 128164066781584759278658159)
  ·
    refine ⟨192246100172377138917987239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128164066781584759278658159 192246100172377138917987239)
    ·
      refine ⟨288369150258565708376980859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192246100172377138917987239 288369150258565708376980859)
      ·
        refine ⟨432553725387848562565471289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288369150258565708376980859 432553725387848562565471289)
        ·
          refine ⟨324415294040886421924103467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 432553725387848562565471289 324415294040886421924103467)
          ·
            refine ⟨486622941061329632886155201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324415294040886421924103467 486622941061329632886155201)
            ·
              refine ⟨364967205795997224664616401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 486622941061329632886155201 364967205795997224664616401)
              ·
                refine ⟨273725404346997918498462301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 364967205795997224664616401 273725404346997918498462301)
                ·
                  refine ⟨102647026630124219436923363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 273725404346997918498462301 102647026630124219436923363)
                  ·
                    refine ⟨153970539945186329155385045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102647026630124219436923363 153970539945186329155385045)
                    ·
                      refine ⟨3608684529965304589579337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 153970539945186329155385045 3608684529965304589579337)
                      ·
                        rfl

theorem cell23_7027888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_7027888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027888 prefixEnd_7027888 := by exact prefixLift 7027888
  have htrace : WordTrace (prefixWord ++ tailWord_7027888) baseStart_7027888 baseEnd_7027888 := by
    simpa [prefixWord, tailWord_7027888, baseEnd_7027888] using wordTrace_append hprefix tailTrace_7027888
  have hstable : (prefixWord ++ tailWord_7027888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027888).length < 2 ^ (prefixWord ++ tailWord_7027888).sum := by decide
  have hdescent : baseEnd_7027888 < baseStart_7027888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027895 : List Nat := [1, 1, 3, 1, 4, 1, 1, 4, 2, 5]
def baseStart_7027895 : Nat := 118140960795 + 7027895 * 2 ^ 59
def prefixEnd_7027895 : Nat := 4983230072969 + 3 ^ 40 * 7027895 * 2
def baseEnd_7027895 : Nat := 1202896041443295354063935

theorem tailTrace_7027895 : CollatzResearch.WordTrace tailWord_7027895 prefixEnd_7027895 1202896041443295354063935 := by
  unfold tailWord_7027895
  simp only [CollatzResearch.WordTrace]
  refine ⟨256328388874144158752821139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170885592582762772501880759 256328388874144158752821139)
  ·
    refine ⟨384492583311216238129231709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256328388874144158752821139 384492583311216238129231709)
    ·
      refine ⟨144184718741706089298461891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384492583311216238129231709 144184718741706089298461891)
      ·
        refine ⟨216277078112559133947692837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144184718741706089298461891 216277078112559133947692837)
        ·
          refine ⟨40551952146104837615192407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216277078112559133947692837 40551952146104837615192407)
          ·
            refine ⟨60827928219157256422788611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40551952146104837615192407 60827928219157256422788611)
            ·
              refine ⟨91241892328735884634182917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60827928219157256422788611 91241892328735884634182917)
              ·
                refine ⟨17107854811637978368909297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91241892328735884634182917 17107854811637978368909297)
                ·
                  refine ⟨12830891108728483776681973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17107854811637978368909297 12830891108728483776681973)
                  ·
                    refine ⟨1202896041443295354063935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12830891108728483776681973 1202896041443295354063935)
                    ·
                      rfl

theorem cell23_7027895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 5].length) (baseStart_7027895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027895 prefixEnd_7027895 := by exact prefixLift 7027895
  have htrace : WordTrace (prefixWord ++ tailWord_7027895) baseStart_7027895 baseEnd_7027895 := by
    simpa [prefixWord, tailWord_7027895, baseEnd_7027895] using wordTrace_append hprefix tailTrace_7027895
  have hstable : (prefixWord ++ tailWord_7027895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027895).length < 2 ^ (prefixWord ++ tailWord_7027895).sum := by decide
  have hdescent : baseEnd_7027895 < baseStart_7027895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027906 : List Nat := [3, 5, 1, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_7027906 : Nat := 118140960795 + 7027906 * 2 ^ 59
def prefixEnd_7027906 : Nat := 4983230072969 + 3 ^ 40 * 7027906 * 2
def baseEnd_7027906 : Nat := 3608693772617085519154255

theorem tailTrace_7027906 : CollatzResearch.WordTrace tailWord_7027906 prefixEnd_7027906 3608693772617085519154255 := by
  unfold tailWord_7027906
  simp only [CollatzResearch.WordTrace]
  refine ⟨64082197519276076907867893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170885860051402871754314381 64082197519276076907867893)
  ·
    refine ⟨6007706017432132210112615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64082197519276076907867893 6007706017432132210112615)
    ·
      refine ⟨9011559026148198315168923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6007706017432132210112615 9011559026148198315168923)
      ·
        refine ⟨13517338539222297472753385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9011559026148198315168923 13517338539222297472753385)
        ·
          refine ⟨10138003904416723104565039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13517338539222297472753385 10138003904416723104565039)
          ·
            refine ⟨15207005856625084656847559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10138003904416723104565039 15207005856625084656847559)
            ·
              refine ⟨22810508784937626985271339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15207005856625084656847559 22810508784937626985271339)
              ·
                refine ⟨34215763177406440477907009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22810508784937626985271339 34215763177406440477907009)
                ·
                  refine ⟨25661822383054830358430257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34215763177406440477907009 25661822383054830358430257)
                  ·
                    refine ⟨19246366787291122768822693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25661822383054830358430257 19246366787291122768822693)
                    ·
                      refine ⟨3608693772617085519154255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19246366787291122768822693 3608693772617085519154255)
                      ·
                        rfl

theorem cell23_7027906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_7027906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027906 prefixEnd_7027906 := by exact prefixLift 7027906
  have htrace : WordTrace (prefixWord ++ tailWord_7027906) baseStart_7027906 baseEnd_7027906 := by
    simpa [prefixWord, tailWord_7027906, baseEnd_7027906] using wordTrace_append hprefix tailTrace_7027906
  have hstable : (prefixWord ++ tailWord_7027906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027906).length < 2 ^ (prefixWord ++ tailWord_7027906).sum := by decide
  have hdescent : baseEnd_7027906 < baseStart_7027906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027910 : List Nat := [6, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_7027910 : Nat := 118140960795 + 7027910 * 2 ^ 59
def prefixEnd_7027910 : Nat := 4983230072969 + 3 ^ 40 * 7027910 * 2
def baseEnd_7027910 : Nat := 3608695826539703503504237

theorem tailTrace_7027910 : CollatzResearch.WordTrace tailWord_7027910 prefixEnd_7027910 3608695826539703503504237 := by
  unfold tailWord_7027910
  simp only [CollatzResearch.WordTrace]
  refine ⟨8010279249034056759831787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 170885957312726544209744789 8010279249034056759831787)
  ·
    refine ⟨12015418873551085139747681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8010279249034056759831787 12015418873551085139747681)
    ·
      refine ⟨9011564155163313854810761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12015418873551085139747681 9011564155163313854810761)
      ·
        refine ⟨6758673116372485391108071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9011564155163313854810761 6758673116372485391108071)
        ·
          refine ⟨10138009674558728086662107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6758673116372485391108071 10138009674558728086662107)
          ·
            refine ⟨15207014511838092129993161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10138009674558728086662107 15207014511838092129993161)
            ·
              refine ⟨11405260883878569097494871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15207014511838092129993161 11405260883878569097494871)
              ·
                refine ⟨17107891325817853646242307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11405260883878569097494871 17107891325817853646242307)
                ·
                  refine ⟨25661836988726780469363461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17107891325817853646242307 25661836988726780469363461)
                  ·
                    refine ⟨4811594435386271338005649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25661836988726780469363461 4811594435386271338005649)
                    ·
                      refine ⟨3608695826539703503504237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4811594435386271338005649 3608695826539703503504237)
                      ·
                        rfl

theorem cell23_7027910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_7027910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027910 prefixEnd_7027910 := by exact prefixLift 7027910
  have htrace : WordTrace (prefixWord ++ tailWord_7027910) baseStart_7027910 baseEnd_7027910 := by
    simpa [prefixWord, tailWord_7027910, baseEnd_7027910] using wordTrace_append hprefix tailTrace_7027910
  have hstable : (prefixWord ++ tailWord_7027910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027910).length < 2 ^ (prefixWord ++ tailWord_7027910).sum := by decide
  have hdescent : baseEnd_7027910 < baseStart_7027910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027949 : List Nat := [1, 5, 1, 2, 2, 1, 1, 2, 2, 4, 2]
def baseStart_7027949 : Nat := 118140960795 + 7027949 * 2 ^ 59
def prefixEnd_7027949 : Nat := 4983230072969 + 3 ^ 40 * 7027949 * 2
def baseEnd_7027949 : Nat := 3608715852285228850916557

theorem tailTrace_7027949 : CollatzResearch.WordTrace tailWord_7027949 prefixEnd_7027949 3608715852285228850916557 := by
  unfold tailWord_7027949
  simp only [CollatzResearch.WordTrace]
  refine ⟨256330358415948525975286901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170886905610632350650191267 256330358415948525975286901)
  ·
    refine ⟨24030971101495174310183147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 256330358415948525975286901 24030971101495174310183147)
    ·
      refine ⟨36046456652242761465274721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24030971101495174310183147 36046456652242761465274721)
      ·
        refine ⟨27034842489182071098956041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36046456652242761465274721 27034842489182071098956041)
        ·
          refine ⟨20276131866886553324217031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27034842489182071098956041 20276131866886553324217031)
          ·
            refine ⟨30414197800329829986325547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20276131866886553324217031 30414197800329829986325547)
            ·
              refine ⟨45621296700494744979488321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30414197800329829986325547 45621296700494744979488321)
              ·
                refine ⟨34215972525371058734616241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45621296700494744979488321 34215972525371058734616241)
                ·
                  refine ⟨25661979394028294050962181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34215972525371058734616241 25661979394028294050962181)
                  ·
                    refine ⟨4811621136380305134555409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25661979394028294050962181 4811621136380305134555409)
                    ·
                      refine ⟨3608715852285228850916557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4811621136380305134555409 3608715852285228850916557)
                      ·
                        rfl

theorem cell23_7027949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_7027949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027949 prefixEnd_7027949 := by exact prefixLift 7027949
  have htrace : WordTrace (prefixWord ++ tailWord_7027949) baseStart_7027949 baseEnd_7027949 := by
    simpa [prefixWord, tailWord_7027949, baseEnd_7027949] using wordTrace_append hprefix tailTrace_7027949
  have hstable : (prefixWord ++ tailWord_7027949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027949).length < 2 ^ (prefixWord ++ tailWord_7027949).sum := by decide
  have hdescent : baseEnd_7027949 < baseStart_7027949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7027955 : List Nat := [1, 1, 1, 2, 2, 6, 1, 1, 8]
def baseStart_7027955 : Nat := 118140960795 + 7027955 * 2 ^ 59
def prefixEnd_7027955 : Nat := 4983230072969 + 3 ^ 40 * 7027955 * 2
def baseEnd_7027955 : Nat := 400968770352128425271281

theorem tailTrace_7027955 : CollatzResearch.WordTrace tailWord_7027955 prefixEnd_7027955 400968770352128425271281 := by
  unfold tailWord_7027955
  simp only [CollatzResearch.WordTrace]
  refine ⟨256330577253926789000005319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170887051502617859333336879 256330577253926789000005319)
  ·
    refine ⟨384495865880890183500007979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256330577253926789000005319 384495865880890183500007979)
    ·
      refine ⟨576743798821335275250011969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384495865880890183500007979 576743798821335275250011969)
      ·
        refine ⟨432557849116001456437508977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 576743798821335275250011969 432557849116001456437508977)
        ·
          refine ⟨324418386837001092328131733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 432557849116001456437508977 324418386837001092328131733)
          ·
            refine ⟨15207111882984426202881175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 324418386837001092328131733 15207111882984426202881175)
            ·
              refine ⟨22810667824476639304321763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15207111882984426202881175 22810667824476639304321763)
              ·
                refine ⟨34216001736714958956482645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22810667824476639304321763 34216001736714958956482645)
                ·
                  refine ⟨400968770352128425271281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34216001736714958956482645 400968770352128425271281)
                  ·
                    rfl

theorem cell23_7027955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 8].length) (baseStart_7027955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7027955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7027955 prefixEnd_7027955 := by exact prefixLift 7027955
  have htrace : WordTrace (prefixWord ++ tailWord_7027955) baseStart_7027955 baseEnd_7027955 := by
    simpa [prefixWord, tailWord_7027955, baseEnd_7027955] using wordTrace_append hprefix tailTrace_7027955
  have hstable : (prefixWord ++ tailWord_7027955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7027955).length < 2 ^ (prefixWord ++ tailWord_7027955).sum := by decide
  have hdescent : baseEnd_7027955 < baseStart_7027955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7027955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028036 : List Nat := [2, 3, 4, 1, 1, 1, 3, 2, 1, 5]
def baseStart_7028036 : Nat := 118140960795 + 7028036 * 2 ^ 59
def prefixEnd_7028036 : Nat := 4983230072969 + 3 ^ 40 * 7028036 * 2
def baseEnd_7028036 : Nat := 1202920175034056670176219

theorem tailTrace_7028036 : CollatzResearch.WordTrace tailWord_7028036 prefixEnd_7028036 1202920175034056670176219 := by
  unfold tailWord_7028036
  simp only [CollatzResearch.WordTrace]
  refine ⟨128166765783316669916851981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170889021044422226555802641 128166765783316669916851981)
  ·
    refine ⟨48062537168743751218819493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128166765783316669916851981 48062537168743751218819493)
    ·
      refine ⟨9011725719139453353528655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48062537168743751218819493 9011725719139453353528655)
      ·
        refine ⟨13517588578709180030292983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9011725719139453353528655 13517588578709180030292983)
        ·
          refine ⟨20276382868063770045439475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13517588578709180030292983 20276382868063770045439475)
          ·
            refine ⟨30414574302095655068159213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20276382868063770045439475 30414574302095655068159213)
            ·
              refine ⟨11405465363285870650559705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30414574302095655068159213 11405465363285870650559705)
              ·
                refine ⟨8554099022464402987919779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11405465363285870650559705 8554099022464402987919779)
                ·
                  refine ⟨12831148533696604481879669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8554099022464402987919779 12831148533696604481879669)
                  ·
                    refine ⟨1202920175034056670176219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12831148533696604481879669 1202920175034056670176219)
                    ·
                      rfl

theorem cell23_7028036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_7028036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028036 prefixEnd_7028036 := by exact prefixLift 7028036
  have htrace : WordTrace (prefixWord ++ tailWord_7028036) baseStart_7028036 baseEnd_7028036 := by
    simpa [prefixWord, tailWord_7028036, baseEnd_7028036] using wordTrace_append hprefix tailTrace_7028036
  have hstable : (prefixWord ++ tailWord_7028036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028036).length < 2 ^ (prefixWord ++ tailWord_7028036).sum := by decide
  have hdescent : baseEnd_7028036 < baseStart_7028036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028039 : List Nat := [1, 1, 4, 1, 2, 3, 3, 2, 1, 1, 4]
def baseStart_7028039 : Nat := 118140960795 + 7028039 * 2 ^ 59
def prefixEnd_7028039 : Nat := 4983230072969 + 3 ^ 40 * 7028039 * 2
def baseEnd_7028039 : Nat := 3608762065544133498791143

theorem tailTrace_7028039 : CollatzResearch.WordTrace tailWord_7028039 prefixEnd_7028039 3608762065544133498791143 := by
  unfold tailWord_7028039
  simp only [CollatzResearch.WordTrace]
  refine ⟨256333640985622471346063171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170889093990414980897375447 256333640985622471346063171)
  ·
    refine ⟨384500461478433707019094757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256333640985622471346063171 384500461478433707019094757)
    ·
      refine ⟨72093836527206320066080267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 384500461478433707019094757 72093836527206320066080267)
      ·
        refine ⟨108140754790809480099120401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72093836527206320066080267 108140754790809480099120401)
        ·
          refine ⟨81105566093107110074340301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108140754790809480099120401 81105566093107110074340301)
          ·
            refine ⟨30414587284915166277877613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81105566093107110074340301 30414587284915166277877613)
            ·
              refine ⟨11405470231843187354204105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30414587284915166277877613 11405470231843187354204105)
              ·
                refine ⟨8554102673882390515653079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11405470231843187354204105 8554102673882390515653079)
                ·
                  refine ⟨12831154010823585773479619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8554102673882390515653079 12831154010823585773479619)
                  ·
                    refine ⟨19246731016235378660219429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12831154010823585773479619 19246731016235378660219429)
                    ·
                      refine ⟨3608762065544133498791143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19246731016235378660219429 3608762065544133498791143)
                      ·
                        rfl

theorem cell23_7028039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_7028039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028039 prefixEnd_7028039 := by exact prefixLift 7028039
  have htrace : WordTrace (prefixWord ++ tailWord_7028039) baseStart_7028039 baseEnd_7028039 := by
    simpa [prefixWord, tailWord_7028039, baseEnd_7028039] using wordTrace_append hprefix tailTrace_7028039
  have hstable : (prefixWord ++ tailWord_7028039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028039).length < 2 ^ (prefixWord ++ tailWord_7028039).sum := by decide
  have hdescent : baseEnd_7028039 < baseStart_7028039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028066 : List Nat := [3, 3, 2, 1, 1, 1, 4, 2, 2, 4]
def baseStart_7028066 : Nat := 118140960795 + 7028066 * 2 ^ 59
def prefixEnd_7028066 : Nat := 4983230072969 + 3 ^ 40 * 7028066 * 2
def baseEnd_7028066 : Nat := 1202925309840601631051173

theorem tailTrace_7028066 : CollatzResearch.WordTrace tailWord_7028066 prefixEnd_7028066 1202925309840601631051173 := by
  unfold tailWord_7028066
  simp only [CollatzResearch.WordTrace]
  refine ⟨64083656439131163739324013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170889750504349769971530701 64083656439131163739324013)
  ·
    refine ⟨24031371164674186402246505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64083656439131163739324013 24031371164674186402246505)
    ·
      refine ⟨18023528373505639801684879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24031371164674186402246505 18023528373505639801684879)
      ·
        refine ⟨27035292560258459702527319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18023528373505639801684879 27035292560258459702527319)
        ·
          refine ⟨40552938840387689553790979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27035292560258459702527319 40552938840387689553790979)
          ·
            refine ⟨60829408260581534330686469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40552938840387689553790979 60829408260581534330686469)
            ·
              refine ⟨11405514048859037687003713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60829408260581534330686469 11405514048859037687003713)
              ·
                refine ⟨8554135536644278265252785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11405514048859037687003713 8554135536644278265252785)
                ·
                  refine ⟨6415601652483208698939589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8554135536644278265252785 6415601652483208698939589)
                  ·
                    refine ⟨1202925309840601631051173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6415601652483208698939589 1202925309840601631051173)
                    ·
                      rfl

theorem cell23_7028066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_7028066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028066 prefixEnd_7028066 := by exact prefixLift 7028066
  have htrace : WordTrace (prefixWord ++ tailWord_7028066) baseStart_7028066 baseEnd_7028066 := by
    simpa [prefixWord, tailWord_7028066, baseEnd_7028066] using wordTrace_append hprefix tailTrace_7028066
  have hstable : (prefixWord ++ tailWord_7028066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028066).length < 2 ^ (prefixWord ++ tailWord_7028066).sum := by decide
  have hdescent : baseEnd_7028066 < baseStart_7028066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028095 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 10]
def baseStart_7028095 : Nat := 118140960795 + 7028095 * 2 ^ 59
def prefixEnd_7028095 : Nat := 4983230072969 + 3 ^ 40 * 7028095 * 2
def baseEnd_7028095 : Nat := 3608790820460785279690885

theorem tailTrace_7028095 : CollatzResearch.WordTrace tailWord_7028095 prefixEnd_7028095 3608790820460785279690885 := by
  unfold tailWord_7028095
  simp only [CollatzResearch.WordTrace]
  refine ⟨256335683473419592910101739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170890455648946395273401159 256335683473419592910101739)
  ·
    refine ⟨384503525210129389365152609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256335683473419592910101739 384503525210129389365152609)
    ·
      refine ⟨288377643907597042023864457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384503525210129389365152609 288377643907597042023864457)
      ·
        refine ⟨216283232930697781517898343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288377643907597042023864457 216283232930697781517898343)
        ·
          refine ⟨324424849396046672276847515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216283232930697781517898343 324424849396046672276847515)
          ·
            refine ⟨486637274094070008415271273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324424849396046672276847515 486637274094070008415271273)
            ·
              refine ⟨364977955570552506311453455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 486637274094070008415271273 364977955570552506311453455)
              ·
                refine ⟨547466933355828759467180183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364977955570552506311453455 547466933355828759467180183)
                ·
                  refine ⟨821200400033743139200770275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 547466933355828759467180183 821200400033743139200770275)
                  ·
                    refine ⟨1231800600050614708801155413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 821200400033743139200770275 1231800600050614708801155413)
                    ·
                      refine ⟨3608790820460785279690885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1231800600050614708801155413 3608790820460785279690885)
                      ·
                        rfl

theorem cell23_7028095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_7028095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028095 prefixEnd_7028095 := by exact prefixLift 7028095
  have htrace : WordTrace (prefixWord ++ tailWord_7028095) baseStart_7028095 baseEnd_7028095 := by
    simpa [prefixWord, tailWord_7028095, baseEnd_7028095] using wordTrace_append hprefix tailTrace_7028095
  have hstable : (prefixWord ++ tailWord_7028095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028095).length < 2 ^ (prefixWord ++ tailWord_7028095).sum := by decide
  have hdescent : baseEnd_7028095 < baseStart_7028095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028110 : List Nat := [4, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3]
def baseStart_7028110 : Nat := 118140960795 + 7028110 * 2 ^ 59
def prefixEnd_7028110 : Nat := 4983230072969 + 3 ^ 40 * 7028110 * 2
def baseEnd_7028110 : Nat := 3608798522670602721003317

theorem tailTrace_7028110 : CollatzResearch.WordTrace tailWord_7028110 prefixEnd_7028110 3608798522670602721003317 := by
  unfold tailWord_7028110
  simp only [CollatzResearch.WordTrace]
  refine ⟨32042028821045656308987223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170890820378910166981265189 32042028821045656308987223)
  ·
    refine ⟨48063043231568484463480835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32042028821045656308987223 48063043231568484463480835)
    ·
      refine ⟨72094564847352726695221253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48063043231568484463480835 72094564847352726695221253)
      ·
        refine ⟨13517730908878636255353985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72094564847352726695221253 13517730908878636255353985)
        ·
          refine ⟨10138298181658977191515489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13517730908878636255353985 10138298181658977191515489)
          ·
            refine ⟨7603723636244232893636617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10138298181658977191515489 7603723636244232893636617)
            ·
              refine ⟨5702792727183174670227463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7603723636244232893636617 5702792727183174670227463)
              ·
                refine ⟨8554189090774762005341195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5702792727183174670227463 8554189090774762005341195)
                ·
                  refine ⟨12831283636162143008011793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8554189090774762005341195 12831283636162143008011793)
                  ·
                    refine ⟨9623462727121607256008845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12831283636162143008011793 9623462727121607256008845)
                    ·
                      refine ⟨3608798522670602721003317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9623462727121607256008845 3608798522670602721003317)
                      ·
                        rfl

theorem cell23_7028110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_7028110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028110 prefixEnd_7028110 := by exact prefixLift 7028110
  have htrace : WordTrace (prefixWord ++ tailWord_7028110) baseStart_7028110 baseEnd_7028110 := by
    simpa [prefixWord, tailWord_7028110, baseEnd_7028110] using wordTrace_append hprefix tailTrace_7028110
  have hstable : (prefixWord ++ tailWord_7028110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028110).length < 2 ^ (prefixWord ++ tailWord_7028110).sum := by decide
  have hdescent : baseEnd_7028110 < baseStart_7028110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028122 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 4, 6]
def baseStart_7028122 : Nat := 118140960795 + 7028122 * 2 ^ 59
def prefixEnd_7028122 : Nat := 4983230072969 + 3 ^ 40 * 7028122 * 2
def baseEnd_7028122 : Nat := 1202934894812818891351087

theorem tailTrace_7028122 : CollatzResearch.WordTrace tailWord_7028122 prefixEnd_7028122 1202934894812818891351087 := by
  unfold tailWord_7028122
  simp only [CollatzResearch.WordTrace]
  refine ⟨64084167061080444130333655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170891112162881184347556413 64084167061080444130333655)
  ·
    refine ⟨96126250591620666195500483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64084167061080444130333655 96126250591620666195500483)
    ·
      refine ⟨144189375887430999293250725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96126250591620666195500483 144189375887430999293250725)
      ·
        refine ⟨27035507978893312367484511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144189375887430999293250725 27035507978893312367484511)
        ·
          refine ⟨40553261968339968551226767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27035507978893312367484511 40553261968339968551226767)
          ·
            refine ⟨60829892952509952826840151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40553261968339968551226767 60829892952509952826840151)
            ·
              refine ⟨91244839428764929240260227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60829892952509952826840151 91244839428764929240260227)
              ·
                refine ⟨136867259143147393860390341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91244839428764929240260227 136867259143147393860390341)
                ·
                  refine ⟨25662611089340136348823189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136867259143147393860390341 25662611089340136348823189)
                  ·
                    refine ⟨1202934894812818891351087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25662611089340136348823189 1202934894812818891351087)
                    ·
                      rfl

theorem cell23_7028122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_7028122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028122 prefixEnd_7028122 := by exact prefixLift 7028122
  have htrace : WordTrace (prefixWord ++ tailWord_7028122) baseStart_7028122 baseEnd_7028122 := by
    simpa [prefixWord, tailWord_7028122, baseEnd_7028122] using wordTrace_append hprefix tailTrace_7028122
  have hstable : (prefixWord ++ tailWord_7028122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028122).length < 2 ^ (prefixWord ++ tailWord_7028122).sum := by decide
  have hdescent : baseEnd_7028122 < baseStart_7028122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028132 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 4, 1, 5]
def baseStart_7028132 : Nat := 118140960795 + 7028132 * 2 ^ 59
def prefixEnd_7028132 : Nat := 4983230072969 + 3 ^ 40 * 7028132 * 2
def baseEnd_7028132 : Nat := 3608809819245001634928215

theorem tailTrace_7028132 : CollatzResearch.WordTrace tailWord_7028132 prefixEnd_7028132 3608809819245001634928215 := by
  unfold tailWord_7028132
  simp only [CollatzResearch.WordTrace]
  refine ⟨128168516487142774114599325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170891355316190365486132433 128168516487142774114599325)
  ·
    refine ⟨48063193682678540292974747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128168516487142774114599325 48063193682678540292974747)
    ·
      refine ⟨72094790524017810439462121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48063193682678540292974747 72094790524017810439462121)
      ·
        refine ⟨54071092893013357829596591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72094790524017810439462121 54071092893013357829596591)
        ·
          refine ⟨81106639339520036744394887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54071092893013357829596591 81106639339520036744394887)
          ·
            refine ⟨121659959009280055116592331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81106639339520036744394887 121659959009280055116592331)
            ·
              refine ⟨182489938513920082674888497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121659959009280055116592331 182489938513920082674888497)
              ·
                refine ⟨136867453885440062006166373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182489938513920082674888497 136867453885440062006166373)
                ·
                  refine ⟨25662647603520011626156195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136867453885440062006166373 25662647603520011626156195)
                  ·
                    refine ⟨38493971405280017439234293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25662647603520011626156195 38493971405280017439234293)
                    ·
                      refine ⟨3608809819245001634928215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38493971405280017439234293 3608809819245001634928215)
                      ·
                        rfl

theorem cell23_7028132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_7028132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028132 prefixEnd_7028132 := by exact prefixLift 7028132
  have htrace : WordTrace (prefixWord ++ tailWord_7028132) baseStart_7028132 baseEnd_7028132 := by
    simpa [prefixWord, tailWord_7028132, baseEnd_7028132] using wordTrace_append hprefix tailTrace_7028132
  have hstable : (prefixWord ++ tailWord_7028132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028132).length < 2 ^ (prefixWord ++ tailWord_7028132).sum := by decide
  have hdescent : baseEnd_7028132 < baseStart_7028132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028152 : List Nat := [2, 1, 2, 1, 2, 2, 4, 2, 7]
def baseStart_7028152 : Nat := 118140960795 + 7028152 * 2 ^ 59
def prefixEnd_7028152 : Nat := 4983230072969 + 3 ^ 40 * 7028152 * 2
def baseEnd_7028152 : Nat := 400980009873121284075347

theorem tailTrace_7028152 : CollatzResearch.WordTrace tailWord_7028152 prefixEnd_7028152 400980009873121284075347 := by
  unfold tailWord_7028152
  simp only [CollatzResearch.WordTrace]
  refine ⟨128168881217106545822463355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170891841622808727763284473 128168881217106545822463355)
  ·
    refine ⟨192253321825659818733695033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128168881217106545822463355 192253321825659818733695033)
    ·
      refine ⟨144189991369244864050271275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192253321825659818733695033 144189991369244864050271275)
      ·
        refine ⟨216284987053867296075406913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144189991369244864050271275 216284987053867296075406913)
        ·
          refine ⟨162213740290400472056555185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216284987053867296075406913 162213740290400472056555185)
          ·
            refine ⟨121660305217800354042416389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162213740290400472056555185 121660305217800354042416389)
            ·
              refine ⟨22811307228337566382953073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121660305217800354042416389 22811307228337566382953073)
              ·
                refine ⟨17108480421253174787214805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22811307228337566382953073 17108480421253174787214805)
                ·
                  refine ⟨400980009873121284075347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17108480421253174787214805 400980009873121284075347)
                  ·
                    rfl

theorem cell23_7028152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 7].length) (baseStart_7028152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028152 prefixEnd_7028152 := by exact prefixLift 7028152
  have htrace : WordTrace (prefixWord ++ tailWord_7028152) baseStart_7028152 baseEnd_7028152 := by
    simpa [prefixWord, tailWord_7028152, baseEnd_7028152] using wordTrace_append hprefix tailTrace_7028152
  have hstable : (prefixWord ++ tailWord_7028152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028152).length < 2 ^ (prefixWord ++ tailWord_7028152).sum := by decide
  have hdescent : baseEnd_7028152 < baseStart_7028152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028197 : List Nat := [1, 3, 1, 5, 1, 3, 2, 1, 2, 2, 2]
def baseStart_7028197 : Nat := 118140960795 + 7028197 * 2 ^ 59
def prefixEnd_7028197 : Nat := 4983230072969 + 3 ^ 40 * 7028197 * 2
def baseEnd_7028197 : Nat := 3608843195487543880615417

theorem tailTrace_7028197 : CollatzResearch.WordTrace tailWord_7028197 prefixEnd_7028197 3608843195487543880615417 := by
  unfold tailWord_7028197
  simp only [CollatzResearch.WordTrace]
  refine ⟨256339403719050064330314845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170892935812700042886876563 256339403719050064330314845)
  ·
    refine ⟨96127276394643774123868067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256339403719050064330314845 96127276394643774123868067)
    ·
      refine ⟨144190914591965661185802101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96127276394643774123868067 144190914591965661185802101)
      ·
        refine ⟨13517898242996780736168947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144190914591965661185802101 13517898242996780736168947)
        ·
          refine ⟨20276847364495171104253421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13517898242996780736168947 20276847364495171104253421)
          ·
            refine ⟨7603817761685689164095033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20276847364495171104253421 7603817761685689164095033)
            ·
              refine ⟨5702863321264266873071275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7603817761685689164095033 5702863321264266873071275)
              ·
                refine ⟨8554294981896400309606913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5702863321264266873071275 8554294981896400309606913)
                ·
                  refine ⟨6415721236422300232205185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8554294981896400309606913 6415721236422300232205185)
                  ·
                    refine ⟨4811790927316725174153889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6415721236422300232205185 4811790927316725174153889)
                    ·
                      refine ⟨3608843195487543880615417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4811790927316725174153889 3608843195487543880615417)
                      ·
                        rfl

theorem cell23_7028197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_7028197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028197 prefixEnd_7028197 := by exact prefixLift 7028197
  have htrace : WordTrace (prefixWord ++ tailWord_7028197) baseStart_7028197 baseEnd_7028197 := by
    simpa [prefixWord, tailWord_7028197, baseEnd_7028197] using wordTrace_append hprefix tailTrace_7028197
  have hstable : (prefixWord ++ tailWord_7028197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028197).length < 2 ^ (prefixWord ++ tailWord_7028197).sum := by decide
  have hdescent : baseEnd_7028197 < baseStart_7028197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028219 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 1, 6, 2]
def baseStart_7028219 : Nat := 118140960795 + 7028219 * 2 ^ 59
def prefixEnd_7028219 : Nat := 4983230072969 + 3 ^ 40 * 7028219 * 2
def baseEnd_7028219 : Nat := 3608854492061942794540315

theorem tailTrace_7028219 : CollatzResearch.WordTrace tailWord_7028219 prefixEnd_7028219 3608854492061942794540315 := by
  unfold tailWord_7028219
  simp only [CollatzResearch.WordTrace]
  refine ⟨256340206124970362087615711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170893470749980241391743807 256340206124970362087615711)
  ·
    refine ⟨384510309187455543131423567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256340206124970362087615711 384510309187455543131423567)
    ·
      refine ⟨576765463781183314697135351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384510309187455543131423567 576765463781183314697135351)
      ·
        refine ⟨865148195671774972045703027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576765463781183314697135351 865148195671774972045703027)
        ·
          refine ⟨1297722293507662458068554541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 865148195671774972045703027 1297722293507662458068554541)
          ·
            refine ⟨486645860065373421775707953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1297722293507662458068554541 486645860065373421775707953)
            ·
              refine ⟨364984395049030066331780965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 486645860065373421775707953 364984395049030066331780965)
              ·
                refine ⟨68434574071693137437208931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 364984395049030066331780965 68434574071693137437208931)
                ·
                  refine ⟨102651861107539706155813397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68434574071693137437208931 102651861107539706155813397)
                  ·
                    refine ⟨4811805989415923726053753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 102651861107539706155813397 4811805989415923726053753)
                    ·
                      refine ⟨3608854492061942794540315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4811805989415923726053753 3608854492061942794540315)
                      ·
                        rfl

theorem cell23_7028219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 6, 2].length) (baseStart_7028219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028219 prefixEnd_7028219 := by exact prefixLift 7028219
  have htrace : WordTrace (prefixWord ++ tailWord_7028219) baseStart_7028219 baseEnd_7028219 := by
    simpa [prefixWord, tailWord_7028219, baseEnd_7028219] using wordTrace_append hprefix tailTrace_7028219
  have hstable : (prefixWord ++ tailWord_7028219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028219).length < 2 ^ (prefixWord ++ tailWord_7028219).sum := by decide
  have hdescent : baseEnd_7028219 < baseStart_7028219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028226 : List Nat := [3, 4, 1, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_7028226 : Nat := 118140960795 + 7028226 * 2 ^ 59
def prefixEnd_7028226 : Nat := 4983230072969 + 3 ^ 40 * 7028226 * 2
def baseEnd_7028226 : Nat := 3608858086426524267152783

theorem tailTrace_7028226 : CollatzResearch.WordTrace tailWord_7028226 prefixEnd_7028226 3608858086426524267152783 := by
  unfold tailWord_7028226
  simp only [CollatzResearch.WordTrace]
  refine ⟨64085115358986250570780133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170893640957296668188747021 64085115358986250570780133)
  ·
    refine ⟨12015959129809921982021275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64085115358986250570780133 12015959129809921982021275)
    ·
      refine ⟨18023938694714882973031913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12015959129809921982021275 18023938694714882973031913)
      ·
        refine ⟨13517954021036162229773935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18023938694714882973031913 13517954021036162229773935)
        ·
          refine ⟨20276931031554243344660903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13517954021036162229773935 20276931031554243344660903)
          ·
            refine ⟨30415396547331365016991355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20276931031554243344660903 30415396547331365016991355)
            ·
              refine ⟨45623094820997047525487033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30415396547331365016991355 45623094820997047525487033)
              ·
                refine ⟨34217321115747785644115275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45623094820997047525487033 34217321115747785644115275)
                ·
                  refine ⟨51325981673621678466172913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34217321115747785644115275 51325981673621678466172913)
                  ·
                    refine ⟨38494486255216258849629685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51325981673621678466172913 38494486255216258849629685)
                    ·
                      refine ⟨3608858086426524267152783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38494486255216258849629685 3608858086426524267152783)
                      ·
                        rfl

theorem cell23_7028226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_7028226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028226 prefixEnd_7028226 := by exact prefixLift 7028226
  have htrace : WordTrace (prefixWord ++ tailWord_7028226) baseStart_7028226 baseEnd_7028226 := by
    simpa [prefixWord, tailWord_7028226, baseEnd_7028226] using wordTrace_append hprefix tailTrace_7028226
  have hstable : (prefixWord ++ tailWord_7028226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028226).length < 2 ^ (prefixWord ++ tailWord_7028226).sum := by decide
  have hdescent : baseEnd_7028226 < baseStart_7028226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028336 : List Nat := [2, 1, 1, 1, 6, 1, 1, 2, 4, 4]
def baseStart_7028336 : Nat := 118140960795 + 7028336 * 2 ^ 59
def prefixEnd_7028336 : Nat := 4983230072969 + 3 ^ 40 * 7028336 * 2
def baseEnd_7028336 : Nat := 1202971523099506278925759

theorem tailTrace_7028336 : CollatzResearch.WordTrace tailWord_7028336 prefixEnd_7028336 1202971523099506278925759 := by
  unfold tailWord_7028336
  simp only [CollatzResearch.WordTrace]
  refine ⟨128172236732773245534812431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170896315643697660713083241 128172236732773245534812431)
  ·
    refine ⟨192258355099159868302218647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128172236732773245534812431 192258355099159868302218647)
    ·
      refine ⟨288387532648739802453327971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192258355099159868302218647 288387532648739802453327971)
      ·
        refine ⟨432581298973109703679991957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288387532648739802453327971 432581298973109703679991957)
        ·
          refine ⟨20277248389364517359999623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 432581298973109703679991957 20277248389364517359999623)
          ·
            refine ⟨30415872584046776039999435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20277248389364517359999623 30415872584046776039999435)
            ·
              refine ⟨45623808876070164059999153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30415872584046776039999435 45623808876070164059999153)
              ·
                refine ⟨34217856657052623044999365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45623808876070164059999153 34217856657052623044999365)
                ·
                  refine ⟨6415848123197366820937381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34217856657052623044999365 6415848123197366820937381)
                  ·
                    refine ⟨1202971523099506278925759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6415848123197366820937381 1202971523099506278925759)
                    ·
                      rfl

theorem cell23_7028336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 4, 4].length) (baseStart_7028336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028336 prefixEnd_7028336 := by exact prefixLift 7028336
  have htrace : WordTrace (prefixWord ++ tailWord_7028336) baseStart_7028336 baseEnd_7028336 := by
    simpa [prefixWord, tailWord_7028336, baseEnd_7028336] using wordTrace_append hprefix tailTrace_7028336
  have hstable : (prefixWord ++ tailWord_7028336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028336).length < 2 ^ (prefixWord ++ tailWord_7028336).sum := by decide
  have hdescent : baseEnd_7028336 < baseStart_7028336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028349 : List Nat := [1, 4, 1, 1, 4, 1, 11]
def baseStart_7028349 : Nat := 118140960795 + 7028349 * 2 ^ 59
def prefixEnd_7028349 : Nat := 4983230072969 + 3 ^ 40 * 7028349 * 2
def baseEnd_7028349 : Nat := 44554583266012682542157

theorem tailTrace_7028349 : CollatzResearch.WordTrace tailWord_7028349 prefixEnd_7028349 44554583266012682542157 := by
  unfold tailWord_7028349
  simp only [CollatzResearch.WordTrace]
  refine ⟨256344947614499394289848101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170896631742999596193232067 256344947614499394289848101)
  ·
    refine ⟨48064677677718636429346519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256344947614499394289848101 48064677677718636429346519)
    ·
      refine ⟨72097016516577954644019779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48064677677718636429346519 72097016516577954644019779)
      ·
        refine ⟨108145524774866931966029669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72097016516577954644019779 108145524774866931966029669)
        ·
          refine ⟨20277285895287549743630563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108145524774866931966029669 20277285895287549743630563)
          ·
            refine ⟨30415928842931324615445845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20277285895287549743630563 30415928842931324615445845)
            ·
              refine ⟨44554583266012682542157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 30415928842931324615445845 44554583266012682542157)
              ·
                rfl

theorem cell23_7028349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 11].length) (baseStart_7028349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028349 prefixEnd_7028349 := by exact prefixLift 7028349
  have htrace : WordTrace (prefixWord ++ tailWord_7028349) baseStart_7028349 baseEnd_7028349 := by
    simpa [prefixWord, tailWord_7028349, baseEnd_7028349] using wordTrace_append hprefix tailTrace_7028349
  have hstable : (prefixWord ++ tailWord_7028349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028349).length < 2 ^ (prefixWord ++ tailWord_7028349).sum := by decide
  have hdescent : baseEnd_7028349 < baseStart_7028349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028366 : List Nat := [4, 1, 1, 3, 1, 3, 2, 8]
def baseStart_7028366 : Nat := 118140960795 + 7028366 * 2 ^ 59
def prefixEnd_7028366 : Nat := 4983230072969 + 3 ^ 40 * 7028366 * 2
def baseEnd_7028366 : Nat := 133664073100672359977857

theorem tailTrace_7028366 : CollatzResearch.WordTrace tailWord_7028366 prefixEnd_7028366 133664073100672359977857 := by
  unfold tailWord_7028366
  simp only [CollatzResearch.WordTrace]
  refine ⟨32043195956929725774152119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170897045103625204128811301 32043195956929725774152119)
  ·
    refine ⟨48064793935394588661228179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32043195956929725774152119 48064793935394588661228179)
    ·
      refine ⟨72097190903091882991842269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48064793935394588661228179 72097190903091882991842269)
      ·
        refine ⟨27036446588659456121940851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72097190903091882991842269 27036446588659456121940851)
        ·
          refine ⟨40554669882989184182911277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27036446588659456121940851 40554669882989184182911277)
          ·
            refine ⟨15208001206120944068591729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40554669882989184182911277 15208001206120944068591729)
            ·
              refine ⟨11406000904590708051443797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15208001206120944068591729 11406000904590708051443797)
              ·
                refine ⟨133664073100672359977857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11406000904590708051443797 133664073100672359977857)
                ·
                  rfl

theorem cell23_7028366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 8].length) (baseStart_7028366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028366 prefixEnd_7028366 := by exact prefixLift 7028366
  have htrace : WordTrace (prefixWord ++ tailWord_7028366) baseStart_7028366 baseEnd_7028366 := by
    simpa [prefixWord, tailWord_7028366, baseEnd_7028366] using wordTrace_append hprefix tailTrace_7028366
  have hstable : (prefixWord ++ tailWord_7028366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028366).length < 2 ^ (prefixWord ++ tailWord_7028366).sum := by decide
  have hdescent : baseEnd_7028366 < baseStart_7028366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028370 : List Nat := [3, 2, 3, 1, 3, 1, 1, 3, 2, 4]
def baseStart_7028370 : Nat := 118140960795 + 7028370 * 2 ^ 59
def prefixEnd_7028370 : Nat := 4983230072969 + 3 ^ 40 * 7028370 * 2
def baseEnd_7028370 : Nat := 1202977342546923901250707

theorem tailTrace_7028370 : CollatzResearch.WordTrace tailWord_7028370 prefixEnd_7028370 1202977342546923901250707 := by
  unfold tailWord_7028370
  simp only [CollatzResearch.WordTrace]
  refine ⟨64086428386855828719090641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170897142364948876584241709 64086428386855828719090641)
  ·
    refine ⟨48064821290141871539317981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64086428386855828719090641 48064821290141871539317981)
    ·
      refine ⟨18024307983803201827244243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48064821290141871539317981 18024307983803201827244243)
      ·
        refine ⟨27036461975704802740866365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18024307983803201827244243 27036461975704802740866365)
        ·
          refine ⟨10138673240889301027824887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27036461975704802740866365 10138673240889301027824887)
          ·
            refine ⟨15208009861333951541737331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10138673240889301027824887 15208009861333951541737331)
            ·
              refine ⟨22812014792000927312605997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15208009861333951541737331 22812014792000927312605997)
              ·
                refine ⟨8554505547000347742227249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22812014792000927312605997 8554505547000347742227249)
                ·
                  refine ⟨6415879160250260806670437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8554505547000347742227249 6415879160250260806670437)
                  ·
                    refine ⟨1202977342546923901250707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6415879160250260806670437 1202977342546923901250707)
                    ·
                      rfl

theorem cell23_7028370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_7028370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028370 prefixEnd_7028370 := by exact prefixLift 7028370
  have htrace : WordTrace (prefixWord ++ tailWord_7028370) baseStart_7028370 baseEnd_7028370 := by
    simpa [prefixWord, tailWord_7028370, baseEnd_7028370] using wordTrace_append hprefix tailTrace_7028370
  have hstable : (prefixWord ++ tailWord_7028370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028370).length < 2 ^ (prefixWord ++ tailWord_7028370).sum := by decide
  have hdescent : baseEnd_7028370 < baseStart_7028370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028389 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 1, 4, 5]
def baseStart_7028389 : Nat := 118140960795 + 7028389 * 2 ^ 59
def prefixEnd_7028389 : Nat := 4983230072969 + 3 ^ 40 * 7028389 * 2
def baseEnd_7028389 : Nat := 3608941783773207129414533

theorem tailTrace_7028389 : CollatzResearch.WordTrace tailWord_7028389 prefixEnd_7028389 3608941783773207129414533 := by
  unfold tailWord_7028389
  simp only [CollatzResearch.WordTrace]
  refine ⟨256346406534354481121304221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170897604356236320747536147 256346406534354481121304221)
  ·
    refine ⟨96129902450382930420489083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256346406534354481121304221 96129902450382930420489083)
    ·
      refine ⟨144194853675574395630733625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96129902450382930420489083 144194853675574395630733625)
      ·
        refine ⟨108146140256680796723050219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144194853675574395630733625 108146140256680796723050219)
        ·
          refine ⟨162219210385021195084575329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108146140256680796723050219 162219210385021195084575329)
          ·
            refine ⟨121664407788765896313431497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162219210385021195084575329 121664407788765896313431497)
            ·
              refine ⟨91248305841574422235073623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121664407788765896313431497 91248305841574422235073623)
              ·
                refine ⟨136872458762361633352610435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91248305841574422235073623 136872458762361633352610435)
                ·
                  refine ⟨205308688143542450028915653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136872458762361633352610435 205308688143542450028915653)
                  ·
                    refine ⟨38495379026914209380421685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 205308688143542450028915653 38495379026914209380421685)
                    ·
                      refine ⟨3608941783773207129414533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38495379026914209380421685 3608941783773207129414533)
                      ·
                        rfl

theorem cell23_7028389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_7028389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028389 prefixEnd_7028389 := by exact prefixLift 7028389
  have htrace : WordTrace (prefixWord ++ tailWord_7028389) baseStart_7028389 baseEnd_7028389 := by
    simpa [prefixWord, tailWord_7028389, baseEnd_7028389] using wordTrace_append hprefix tailTrace_7028389
  have hstable : (prefixWord ++ tailWord_7028389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028389).length < 2 ^ (prefixWord ++ tailWord_7028389).sum := by decide
  have hdescent : baseEnd_7028389 < baseStart_7028389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028410 : List Nat := [3, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3]
def baseStart_7028410 : Nat := 118140960795 + 7028410 * 2 ^ 59
def prefixEnd_7028410 : Nat := 4983230072969 + 3 ^ 40 * 7028410 * 2
def baseEnd_7028410 : Nat := 3608952566866951547251937

theorem tailTrace_7028410 : CollatzResearch.WordTrace tailWord_7028410 prefixEnd_7028410 3608952566866951547251937 := by
  unfold tailWord_7028410
  simp only [CollatzResearch.WordTrace]
  refine ⟨64086793116819600426954671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170898114978185601138545789 64086793116819600426954671)
  ·
    refine ⟨96130189675229400640432007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64086793116819600426954671 96130189675229400640432007)
    ·
      refine ⟨144195284512844100960648011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96130189675229400640432007 144195284512844100960648011)
      ·
        refine ⟨216292926769266151440972017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144195284512844100960648011 216292926769266151440972017)
        ·
          refine ⟨162219695076949613580729013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216292926769266151440972017 162219695076949613580729013)
          ·
            refine ⟨15208096413464026273193345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162219695076949613580729013 15208096413464026273193345)
            ·
              refine ⟨11406072310098019704895009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15208096413464026273193345 11406072310098019704895009)
              ·
                refine ⟨8554554232573514778671257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11406072310098019704895009 8554554232573514778671257)
                ·
                  refine ⟨6415915674430136084003443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8554554232573514778671257 6415915674430136084003443)
                  ·
                    refine ⟨9623873511645204126005165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6415915674430136084003443 9623873511645204126005165)
                    ·
                      refine ⟨3608952566866951547251937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9623873511645204126005165 3608952566866951547251937)
                      ·
                        rfl

theorem cell23_7028410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3].length) (baseStart_7028410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028410 prefixEnd_7028410 := by exact prefixLift 7028410
  have htrace : WordTrace (prefixWord ++ tailWord_7028410) baseStart_7028410 baseEnd_7028410 := by
    simpa [prefixWord, tailWord_7028410, baseEnd_7028410] using wordTrace_append hprefix tailTrace_7028410
  have hstable : (prefixWord ++ tailWord_7028410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028410).length < 2 ^ (prefixWord ++ tailWord_7028410).sum := by decide
  have hdescent : baseEnd_7028410 < baseStart_7028410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028433 : List Nat := [1, 2, 2, 1, 2, 4, 1, 3, 1, 4, 2]
def baseStart_7028433 : Nat := 118140960795 + 7028433 * 2 ^ 59
def prefixEnd_7028433 : Nat := 4983230072969 + 3 ^ 40 * 7028433 * 2
def baseEnd_7028433 : Nat := 3608964376922004957264331

theorem tailTrace_7028433 : CollatzResearch.WordTrace tailWord_7028433 prefixEnd_7028433 3608964376922004957264331 := by
  unfold tailWord_7028433
  simp only [CollatzResearch.WordTrace]
  refine ⟨256348011346195076635905953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170898674230796717757270635 256348011346195076635905953)
  ·
    refine ⟨192261008509646307476929465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256348011346195076635905953 192261008509646307476929465)
    ·
      refine ⟨144195756382234730607697099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192261008509646307476929465 144195756382234730607697099)
      ·
        refine ⟨216293634573352095911545649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144195756382234730607697099 216293634573352095911545649)
        ·
          refine ⟨162220225930014071933659237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216293634573352095911545649 162220225930014071933659237)
          ·
            refine ⟨30416292361877638487561107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162220225930014071933659237 30416292361877638487561107)
            ·
              refine ⟨45624438542816457731341661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30416292361877638487561107 45624438542816457731341661)
              ·
                refine ⟨17109164453556171649253123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45624438542816457731341661 17109164453556171649253123)
                ·
                  refine ⟨25663746680334257473879685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17109164453556171649253123 25663746680334257473879685)
                  ·
                    refine ⟨4811952502562673276352441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25663746680334257473879685 4811952502562673276352441)
                    ·
                      refine ⟨3608964376922004957264331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4811952502562673276352441 3608964376922004957264331)
                      ·
                        rfl

theorem cell23_7028433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 4, 2].length) (baseStart_7028433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028433 prefixEnd_7028433 := by exact prefixLift 7028433
  have htrace : WordTrace (prefixWord ++ tailWord_7028433) baseStart_7028433 baseEnd_7028433 := by
    simpa [prefixWord, tailWord_7028433, baseEnd_7028433] using wordTrace_append hprefix tailTrace_7028433
  have hstable : (prefixWord ++ tailWord_7028433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028433).length < 2 ^ (prefixWord ++ tailWord_7028433).sum := by decide
  have hdescent : baseEnd_7028433 < baseStart_7028433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028484 : List Nat := [2, 3, 2, 2, 1, 3, 3, 1, 2, 2, 2]
def baseStart_7028484 : Nat := 118140960795 + 7028484 * 2 ^ 59
def prefixEnd_7028484 : Nat := 4983230072969 + 3 ^ 40 * 7028484 * 2
def baseEnd_7028484 : Nat := 3608990564435384257726597

theorem tailTrace_7028484 : CollatzResearch.WordTrace tailWord_7028484 prefixEnd_7028484 3608990564435384257726597 := by
  unfold tailWord_7028484
  simp only [CollatzResearch.WordTrace]
  refine ⟨128174935734505156173006253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170899914312673541564008337 128174935734505156173006253)
  ·
    refine ⟨48065600900439433564877345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128174935734505156173006253 48065600900439433564877345)
    ·
      refine ⟨36049200675329575173658009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48065600900439433564877345 36049200675329575173658009)
      ·
        refine ⟨27036900506497181380243507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36049200675329575173658009 27036900506497181380243507)
        ·
          refine ⟨40555350759745772070365261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27036900506497181380243507 40555350759745772070365261)
          ·
            refine ⟨15208256534904664526386973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40555350759745772070365261 15208256534904664526386973)
            ·
              refine ⟨5703096200589249197395115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15208256534904664526386973 5703096200589249197395115)
              ·
                refine ⟨8554644300883873796092673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5703096200589249197395115 8554644300883873796092673)
                ·
                  refine ⟨6415983225662905347069505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8554644300883873796092673 6415983225662905347069505)
                  ·
                    refine ⟨4811987419247179010302129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6415983225662905347069505 4811987419247179010302129)
                    ·
                      refine ⟨3608990564435384257726597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4811987419247179010302129 3608990564435384257726597)
                      ·
                        rfl

theorem cell23_7028484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_7028484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028484 prefixEnd_7028484 := by exact prefixLift 7028484
  have htrace : WordTrace (prefixWord ++ tailWord_7028484) baseStart_7028484 baseEnd_7028484 := by
    simpa [prefixWord, tailWord_7028484, baseEnd_7028484] using wordTrace_append hprefix tailTrace_7028484
  have hstable : (prefixWord ++ tailWord_7028484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028484).length < 2 ^ (prefixWord ++ tailWord_7028484).sum := by decide
  have hdescent : baseEnd_7028484 < baseStart_7028484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028557 : List Nat := [1, 6, 1, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_7028557 : Nat := 118140960795 + 7028557 * 2 ^ 59
def prefixEnd_7028557 : Nat := 4983230072969 + 3 ^ 40 * 7028557 * 2
def baseEnd_7028557 : Nat := 3609028048523162472113761

theorem tailTrace_7028557 : CollatzResearch.WordTrace tailWord_7028557 prefixEnd_7028557 3609028048523162472113761 := by
  unfold tailWord_7028557
  simp only [CollatzResearch.WordTrace]
  refine ⟨256352533997745845813419925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170901689331830563875613283 256352533997745845813419925)
  ·
    refine ⟨12016525031144336522504059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 256352533997745845813419925 12016525031144336522504059)
    ·
      refine ⟨18024787546716504783756089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12016525031144336522504059 18024787546716504783756089)
      ·
        refine ⟨13518590660037378587817067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18024787546716504783756089 13518590660037378587817067)
        ·
          refine ⟨20277885990056067881725601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13518590660037378587817067 20277885990056067881725601)
          ·
            refine ⟨15208414492542050911294201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20277885990056067881725601 15208414492542050911294201)
            ·
              refine ⟨11406310869406538183470651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15208414492542050911294201 11406310869406538183470651)
              ·
                refine ⟨17109466304109807275205977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11406310869406538183470651 17109466304109807275205977)
                ·
                  refine ⟨12832099728082355456404483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17109466304109807275205977 12832099728082355456404483)
                  ·
                    refine ⟨19248149592123533184606725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12832099728082355456404483 19248149592123533184606725)
                    ·
                      refine ⟨3609028048523162472113761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19248149592123533184606725 3609028048523162472113761)
                      ·
                        rfl

theorem cell23_7028557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_7028557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028557 prefixEnd_7028557 := by exact prefixLift 7028557
  have htrace : WordTrace (prefixWord ++ tailWord_7028557) baseStart_7028557 baseEnd_7028557 := by
    simpa [prefixWord, tailWord_7028557, baseEnd_7028557] using wordTrace_append hprefix tailTrace_7028557
  have hstable : (prefixWord ++ tailWord_7028557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028557).length < 2 ^ (prefixWord ++ tailWord_7028557).sum := by decide
  have hdescent : baseEnd_7028557 < baseStart_7028557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028580 : List Nat := [2, 3, 1, 1, 5, 1, 2, 2, 6]
def baseStart_7028580 : Nat := 118140960795 + 7028580 * 2 ^ 59
def prefixEnd_7028580 : Nat := 4983230072969 + 3 ^ 40 * 7028580 * 2
def baseEnd_7028580 : Nat := 401004428730912875791795

theorem tailTrace_7028580 : CollatzResearch.WordTrace tailWord_7028580 prefixEnd_7028580 401004428730912875791795 := by
  unfold tailWord_7028580
  simp only [CollatzResearch.WordTrace]
  refine ⟨128176686438331260370753597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170902248584441680494338129 128176686438331260370753597)
  ·
    refine ⟨48066257414374222639032599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128176686438331260370753597 48066257414374222639032599)
    ·
      refine ⟨72099386121561333958548899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48066257414374222639032599 72099386121561333958548899)
      ·
        refine ⟨108149079182342000937823349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72099386121561333958548899 108149079182342000937823349)
        ·
          refine ⟨10138976173344562587920939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108149079182342000937823349 10138976173344562587920939)
          ·
            refine ⟨15208464260016843881881409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10138976173344562587920939 15208464260016843881881409)
            ·
              refine ⟨11406348195012632911411057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15208464260016843881881409 11406348195012632911411057)
              ·
                refine ⟨8554761146259474683558293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11406348195012632911411057 8554761146259474683558293)
                ·
                  refine ⟨401004428730912875791795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8554761146259474683558293 401004428730912875791795)
                  ·
                    rfl

theorem cell23_7028580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_7028580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028580 prefixEnd_7028580 := by exact prefixLift 7028580
  have htrace : WordTrace (prefixWord ++ tailWord_7028580) baseStart_7028580 baseEnd_7028580 := by
    simpa [prefixWord, tailWord_7028580, baseEnd_7028580] using wordTrace_append hprefix tailTrace_7028580
  have hstable : (prefixWord ++ tailWord_7028580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028580).length < 2 ^ (prefixWord ++ tailWord_7028580).sum := by decide
  have hdescent : baseEnd_7028580 < baseStart_7028580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028613 : List Nat := [1, 3, 1, 1, 3, 2, 1, 3, 3, 1, 4]
def baseStart_7028613 : Nat := 118140960795 + 7028613 * 2 ^ 59
def prefixEnd_7028613 : Nat := 4983230072969 + 3 ^ 40 * 7028613 * 2
def baseEnd_7028613 : Nat := 3609056803439814253013503

theorem tailTrace_7028613 : CollatzResearch.WordTrace tailWord_7028613 prefixEnd_7028613 3609056803439814253013503 := by
  unfold tailWord_7028613
  simp only [CollatzResearch.WordTrace]
  refine ⟨256354576485542967377458493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170903050990361978251638995 256354576485542967377458493)
  ·
    refine ⟨96132966182078612766546935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256354576485542967377458493 96132966182078612766546935)
    ·
      refine ⟨144199449273117919149820403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96132966182078612766546935 144199449273117919149820403)
      ·
        refine ⟨216299173909676878724730605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144199449273117919149820403 216299173909676878724730605)
        ·
          refine ⟨81112190216128829521773977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216299173909676878724730605 81112190216128829521773977)
          ·
            refine ⟨60834142662096622141330483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81112190216128829521773977 60834142662096622141330483)
            ·
              refine ⟨91251213993144933211995725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60834142662096622141330483 91251213993144933211995725)
              ·
                refine ⟨34219205247429349954498397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91251213993144933211995725 34219205247429349954498397)
                ·
                  refine ⟨12832201967786006232936899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34219205247429349954498397 12832201967786006232936899)
                  ·
                    refine ⟨19248302951679009349405349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12832201967786006232936899 19248302951679009349405349)
                    ·
                      refine ⟨3609056803439814253013503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19248302951679009349405349 3609056803439814253013503)
                      ·
                        rfl

theorem cell23_7028613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_7028613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028613 prefixEnd_7028613 := by exact prefixLift 7028613
  have htrace : WordTrace (prefixWord ++ tailWord_7028613) baseStart_7028613 baseEnd_7028613 := by
    simpa [prefixWord, tailWord_7028613, baseEnd_7028613] using wordTrace_append hprefix tailTrace_7028613
  have hstable : (prefixWord ++ tailWord_7028613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028613).length < 2 ^ (prefixWord ++ tailWord_7028613).sum := by decide
  have hdescent : baseEnd_7028613 < baseStart_7028613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028670 : List Nat := [4, 2, 1, 1, 1, 3, 4, 7]
def baseStart_7028670 : Nat := 118140960795 + 7028670 * 2 ^ 59
def prefixEnd_7028670 : Nat := 4983230072969 + 3 ^ 40 * 7028670 * 2
def baseEnd_7028670 : Nat := 133669854512485945555583

theorem tailTrace_7028670 : CollatzResearch.WordTrace tailWord_7028670 prefixEnd_7028670 133669854512485945555583 := by
  unfold tailWord_7028670
  simp only [CollatzResearch.WordTrace]
  refine ⟨32044581930792058264035433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170904436964224310741522309 32044581930792058264035433)
  ·
    refine ⟨24033436448094043698026575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32044581930792058264035433 24033436448094043698026575)
    ·
      refine ⟨36050154672141065547039863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24033436448094043698026575 36050154672141065547039863)
      ·
        refine ⟨54075232008211598320559795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36050154672141065547039863 54075232008211598320559795)
        ·
          refine ⟨81112848012317397480839693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54075232008211598320559795 81112848012317397480839693)
          ·
            refine ⟨30417318004619024055314885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81112848012317397480839693 30417318004619024055314885)
            ·
              refine ⟨5703247125866067010371541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30417318004619024055314885 5703247125866067010371541)
              ·
                refine ⟨133669854512485945555583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5703247125866067010371541 133669854512485945555583)
                ·
                  rfl

theorem cell23_7028670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 7].length) (baseStart_7028670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028670 prefixEnd_7028670 := by exact prefixLift 7028670
  have htrace : WordTrace (prefixWord ++ tailWord_7028670) baseStart_7028670 baseEnd_7028670 := by
    simpa [prefixWord, tailWord_7028670, baseEnd_7028670] using wordTrace_append hprefix tailTrace_7028670
  have hstable : (prefixWord ++ tailWord_7028670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028670).length < 2 ^ (prefixWord ++ tailWord_7028670).sum := by decide
  have hdescent : baseEnd_7028670 < baseStart_7028670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028698 : List Nat := [3, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2]
def baseStart_7028698 : Nat := 118140960795 + 7028698 * 2 ^ 59
def prefixEnd_7028698 : Nat := 4983230072969 + 3 ^ 40 * 7028698 * 2
def baseEnd_7028698 : Nat := 3609100449295446420450613

theorem tailTrace_7028698 : CollatzResearch.WordTrace tailWord_7028698 prefixEnd_7028698 3609100449295446420450613 := by
  unfold tailWord_7028698
  simp only [CollatzResearch.WordTrace]
  refine ⟨64089419172558756723575687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170905117793490017929535165 64089419172558756723575687)
  ·
    refine ⟨96134128758838135085363531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64089419172558756723575687 96134128758838135085363531)
    ·
      refine ⟨144201193138257202628045297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96134128758838135085363531 144201193138257202628045297)
      ·
        refine ⟨108150894853692901971033973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144201193138257202628045297 108150894853692901971033973)
        ·
          refine ⟨10139146392533709559784435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108150894853692901971033973 10139146392533709559784435)
          ·
            refine ⟨15208719588800564339676653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10139146392533709559784435 15208719588800564339676653)
            ·
              refine ⟨5703269845800211627378745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15208719588800564339676653 5703269845800211627378745)
              ·
                refine ⟨4277452384350158720534059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5703269845800211627378745 4277452384350158720534059)
                ·
                  refine ⟨6416178576525238080801089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4277452384350158720534059 6416178576525238080801089)
                  ·
                    refine ⟨4812133932393928560600817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6416178576525238080801089 4812133932393928560600817)
                    ·
                      refine ⟨3609100449295446420450613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4812133932393928560600817 3609100449295446420450613)
                      ·
                        rfl

theorem cell23_7028698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2].length) (baseStart_7028698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028698 prefixEnd_7028698 := by exact prefixLift 7028698
  have htrace : WordTrace (prefixWord ++ tailWord_7028698) baseStart_7028698 baseEnd_7028698 := by
    simpa [prefixWord, tailWord_7028698, baseEnd_7028698] using wordTrace_append hprefix tailTrace_7028698
  have hstable : (prefixWord ++ tailWord_7028698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028698).length < 2 ^ (prefixWord ++ tailWord_7028698).sum := by decide
  have hdescent : baseEnd_7028698 < baseStart_7028698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028737 : List Nat := [1, 2, 4, 1, 2, 1, 3, 2, 1, 4, 2]
def baseStart_7028737 : Nat := 118140960795 + 7028737 * 2 ^ 59
def prefixEnd_7028737 : Nat := 4983230072969 + 3 ^ 40 * 7028737 * 2
def baseEnd_7028737 : Nat := 3609120475040971767862933

theorem tailTrace_7028737 : CollatzResearch.WordTrace tailWord_7028737 prefixEnd_7028737 3609120475040971767862933 := by
  unfold tailWord_7028737
  simp only [CollatzResearch.WordTrace]
  refine ⟨256359099137093736554972465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170906066091395824369981643 256359099137093736554972465)
  ·
    refine ⟨192269324352820302416229349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256359099137093736554972465 192269324352820302416229349)
    ·
      refine ⟨36050498316153806703043003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192269324352820302416229349 36050498316153806703043003)
      ·
        refine ⟨54075747474230710054564505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36050498316153806703043003 54075747474230710054564505)
        ·
          refine ⟨40556810605673032540923379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54075747474230710054564505 40556810605673032540923379)
          ·
            refine ⟨60835215908509548811385069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40556810605673032540923379 60835215908509548811385069)
            ·
              refine ⟨22813205965691080804269401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60835215908509548811385069 22813205965691080804269401)
              ·
                refine ⟨17109904474268310603202051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22813205965691080804269401 17109904474268310603202051)
                ·
                  refine ⟨25664856711402465904803077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17109904474268310603202051 25664856711402465904803077)
                  ·
                    refine ⟨4812160633387962357150577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25664856711402465904803077 4812160633387962357150577)
                    ·
                      refine ⟨3609120475040971767862933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4812160633387962357150577 3609120475040971767862933)
                      ·
                        rfl

theorem cell23_7028737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_7028737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028737 prefixEnd_7028737 := by exact prefixLift 7028737
  have htrace : WordTrace (prefixWord ++ tailWord_7028737) baseStart_7028737 baseEnd_7028737 := by
    simpa [prefixWord, tailWord_7028737, baseEnd_7028737] using wordTrace_append hprefix tailTrace_7028737
  have hstable : (prefixWord ++ tailWord_7028737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028737).length < 2 ^ (prefixWord ++ tailWord_7028737).sum := by decide
  have hdescent : baseEnd_7028737 < baseStart_7028737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028749 : List Nat := [1, 7, 1, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_7028749 : Nat := 118140960795 + 7028749 * 2 ^ 59
def prefixEnd_7028749 : Nat := 4983230072969 + 3 ^ 40 * 7028749 * 2
def baseEnd_7028749 : Nat := 3609126636808825720912879

theorem tailTrace_7028749 : CollatzResearch.WordTrace tailWord_7028749 prefixEnd_7028749 3609126636808825720912879 := by
  unfold tailWord_7028749
  simp only [CollatzResearch.WordTrace]
  refine ⟨256359536813050262604409301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170906357875366841736272867 256359536813050262604409301)
  ·
    refine ⟨6008426644055865529790843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 256359536813050262604409301 6008426644055865529790843)
    ·
      refine ⟨9012639966083798294686265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6008426644055865529790843 9012639966083798294686265)
      ·
        refine ⟨6759479974562848721014699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9012639966083798294686265 6759479974562848721014699)
        ·
          refine ⟨10139219961844273081522049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6759479974562848721014699 10139219961844273081522049)
          ·
            refine ⟨7604414971383204811141537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10139219961844273081522049 7604414971383204811141537)
            ·
              refine ⟨5703311228537403608356153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7604414971383204811141537 5703311228537403608356153)
              ·
                refine ⟨4277483421403052706267115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5703311228537403608356153 4277483421403052706267115)
                ·
                  refine ⟨6416225132104579059400673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4277483421403052706267115 6416225132104579059400673)
                  ·
                    refine ⟨4812168849078434294550505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6416225132104579059400673 4812168849078434294550505)
                    ·
                      refine ⟨3609126636808825720912879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4812168849078434294550505 3609126636808825720912879)
                      ·
                        rfl

theorem cell23_7028749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_7028749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028749 prefixEnd_7028749 := by exact prefixLift 7028749
  have htrace : WordTrace (prefixWord ++ tailWord_7028749) baseStart_7028749 baseEnd_7028749 := by
    simpa [prefixWord, tailWord_7028749, baseEnd_7028749] using wordTrace_append hprefix tailTrace_7028749
  have hstable : (prefixWord ++ tailWord_7028749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028749).length < 2 ^ (prefixWord ++ tailWord_7028749).sum := by decide
  have hdescent : baseEnd_7028749 < baseStart_7028749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028750 : List Nat := [4, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4]
def baseStart_7028750 : Nat := 118140960795 + 7028750 * 2 ^ 59
def prefixEnd_7028750 : Nat := 4983230072969 + 3 ^ 40 * 7028750 * 2
def baseEnd_7028750 : Nat := 3609127150289480217000373

theorem tailTrace_7028750 : CollatzResearch.WordTrace tailWord_7028750 prefixEnd_7028750 3609127150289480217000373 := by
  unfold tailWord_7028750
  simp only [CollatzResearch.WordTrace]
  refine ⟨32044946660755829971899463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170906382190697759850130469 32044946660755829971899463)
  ·
    refine ⟨48067419991133744957849195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32044946660755829971899463 48067419991133744957849195)
    ·
      refine ⟨72101129986700617436773793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48067419991133744957849195 72101129986700617436773793)
      ·
        refine ⟨54075847490025463077580345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72101129986700617436773793 54075847490025463077580345)
        ·
          refine ⟨40556885617519097308185259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54075847490025463077580345 40556885617519097308185259)
          ·
            refine ⟨60835328426278645962277889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40556885617519097308185259 60835328426278645962277889)
            ·
              refine ⟨45626496319708984471708417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60835328426278645962277889 45626496319708984471708417)
              ·
                refine ⟨34219872239781738353781313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45626496319708984471708417 34219872239781738353781313)
                ·
                  refine ⟨25664904179836303765335985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34219872239781738353781313 25664904179836303765335985)
                  ·
                    refine ⟨19248678134877227824001989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25664904179836303765335985 19248678134877227824001989)
                    ·
                      refine ⟨3609127150289480217000373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19248678134877227824001989 3609127150289480217000373)
                      ·
                        rfl

theorem cell23_7028750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_7028750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028750 prefixEnd_7028750 := by exact prefixLift 7028750
  have htrace : WordTrace (prefixWord ++ tailWord_7028750) baseStart_7028750 baseEnd_7028750 := by
    simpa [prefixWord, tailWord_7028750, baseEnd_7028750] using wordTrace_append hprefix tailTrace_7028750
  have hstable : (prefixWord ++ tailWord_7028750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028750).length < 2 ^ (prefixWord ++ tailWord_7028750).sum := by decide
  have hdescent : baseEnd_7028750 < baseStart_7028750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028783 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 5]
def baseStart_7028783 : Nat := 118140960795 + 7028783 * 2 ^ 59
def prefixEnd_7028783 : Nat := 4983230072969 + 3 ^ 40 * 7028783 * 2
def baseEnd_7028783 : Nat := 3609144095151078587887721

theorem tailTrace_7028783 : CollatzResearch.WordTrace tailWord_7028783 prefixEnd_7028783 3609144095151078587887721 := by
  unfold tailWord_7028783
  simp only [CollatzResearch.WordTrace]
  refine ⟨256360776894927086411147003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170907184596618057607431335 256360776894927086411147003)
  ·
    refine ⟨384541165342390629616720505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256360776894927086411147003 384541165342390629616720505)
    ·
      refine ⟨288405874006792972212540379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384541165342390629616720505 288405874006792972212540379)
      ·
        refine ⟨432608811010189458318810569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288405874006792972212540379 432608811010189458318810569)
        ·
          refine ⟨324456608257642093739107927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 432608811010189458318810569 324456608257642093739107927)
          ·
            refine ⟨486684912386463140608661891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324456608257642093739107927 486684912386463140608661891)
            ·
              refine ⟨730027368579694710912992837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486684912386463140608661891 730027368579694710912992837)
              ·
                refine ⟨136880131608692758296186157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 730027368579694710912992837 136880131608692758296186157)
                ·
                  refine ⟨51330049353259784361069809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136880131608692758296186157 51330049353259784361069809)
                  ·
                    refine ⟨38497537014944838270802357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51330049353259784361069809 38497537014944838270802357)
                    ·
                      refine ⟨3609144095151078587887721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38497537014944838270802357 3609144095151078587887721)
                      ·
                        rfl

theorem cell23_7028783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 5].length) (baseStart_7028783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028783 prefixEnd_7028783 := by exact prefixLift 7028783
  have htrace : WordTrace (prefixWord ++ tailWord_7028783) baseStart_7028783 baseEnd_7028783 := by
    simpa [prefixWord, tailWord_7028783, baseEnd_7028783] using wordTrace_append hprefix tailTrace_7028783
  have hstable : (prefixWord ++ tailWord_7028783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028783).length < 2 ^ (prefixWord ++ tailWord_7028783).sum := by decide
  have hdescent : baseEnd_7028783 < baseStart_7028783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028810 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 4, 1, 4]
def baseStart_7028810 : Nat := 118140960795 + 7028810 * 2 ^ 59
def prefixEnd_7028810 : Nat := 4983230072969 + 3 ^ 40 * 7028810 * 2
def baseEnd_7028810 : Nat := 3609157959128749982250097

theorem tailTrace_7028810 : CollatzResearch.WordTrace tailWord_7028810 prefixEnd_7028810 3609157959128749982250097 := by
  unfold tailWord_7028810
  simp only [CollatzResearch.WordTrace]
  refine ⟨64090440416457317505594971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170907841110552846681586589 64090440416457317505594971)
  ·
    refine ⟨96135660624685976258392457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64090440416457317505594971 96135660624685976258392457)
    ·
      refine ⟨72101745468514482193794343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96135660624685976258392457 72101745468514482193794343)
      ·
        refine ⟨108152618202771723290691515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72101745468514482193794343 108152618202771723290691515)
        ·
          refine ⟨162228927304157584936037273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108152618202771723290691515 162228927304157584936037273)
          ·
            refine ⟨121671695478118188702027955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162228927304157584936037273 121671695478118188702027955)
            ·
              refine ⟨182507543217177283053041933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121671695478118188702027955 182507543217177283053041933)
              ·
                refine ⟨68440328706441481144890725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182507543217177283053041933 68440328706441481144890725)
                ·
                  refine ⟨12832561632457777714667011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68440328706441481144890725 12832561632457777714667011)
                  ·
                    refine ⟨19248842448686666572000517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12832561632457777714667011 19248842448686666572000517)
                    ·
                      refine ⟨3609157959128749982250097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19248842448686666572000517 3609157959128749982250097)
                      ·
                        rfl

theorem cell23_7028810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_7028810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028810 prefixEnd_7028810 := by exact prefixLift 7028810
  have htrace : WordTrace (prefixWord ++ tailWord_7028810) baseStart_7028810 baseEnd_7028810 := by
    simpa [prefixWord, tailWord_7028810, baseEnd_7028810] using wordTrace_append hprefix tailTrace_7028810
  have hstable : (prefixWord ++ tailWord_7028810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028810).length < 2 ^ (prefixWord ++ tailWord_7028810).sum := by decide
  have hdescent : baseEnd_7028810 < baseStart_7028810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028837 : List Nat := [1, 3, 1, 3, 2, 2, 2, 2, 3, 4]
def baseStart_7028837 : Nat := 118140960795 + 7028837 * 2 ^ 59
def prefixEnd_7028837 : Nat := 4983230072969 + 3 ^ 40 * 7028837 * 2
def baseEnd_7028837 : Nat := 1203057274368807125537491

theorem tailTrace_7028837 : CollatzResearch.WordTrace tailWord_7028837 prefixEnd_7028837 1203057274368807125537491 := by
  unfold tailWord_7028837
  simp only [CollatzResearch.WordTrace]
  refine ⟨256362746436731453633612765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170908497624487635755741843 256362746436731453633612765)
  ·
    refine ⟨96136029913774295112604787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256362746436731453633612765 96136029913774295112604787)
    ·
      refine ⟨144204044870661442668907181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96136029913774295112604787 144204044870661442668907181)
      ·
        refine ⟨54076516826498041000840193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144204044870661442668907181 54076516826498041000840193)
        ·
          refine ⟨40557387619873530750630145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54076516826498041000840193 40557387619873530750630145)
          ·
            refine ⟨30418040714905148062972609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40557387619873530750630145 30418040714905148062972609)
            ·
              refine ⟨22813530536178861047229457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30418040714905148062972609 22813530536178861047229457)
              ·
                refine ⟨17110147902134145785422093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22813530536178861047229457 17110147902134145785422093)
                ·
                  refine ⟨6416305463300304669533285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17110147902134145785422093 6416305463300304669533285)
                  ·
                    refine ⟨1203057274368807125537491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6416305463300304669533285 1203057274368807125537491)
                    ·
                      rfl

theorem cell23_7028837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 4].length) (baseStart_7028837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028837 prefixEnd_7028837 := by exact prefixLift 7028837
  have htrace : WordTrace (prefixWord ++ tailWord_7028837) baseStart_7028837 baseEnd_7028837 := by
    simpa [prefixWord, tailWord_7028837, baseEnd_7028837] using wordTrace_append hprefix tailTrace_7028837
  have hstable : (prefixWord ++ tailWord_7028837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028837).length < 2 ^ (prefixWord ++ tailWord_7028837).sum := by decide
  have hdescent : baseEnd_7028837 < baseStart_7028837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028843 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 9]
def baseStart_7028843 : Nat := 118140960795 + 7028843 * 2 ^ 59
def prefixEnd_7028843 : Nat := 4983230072969 + 3 ^ 40 * 7028843 * 2
def baseEnd_7028843 : Nat := 3609174903990348353137445

theorem tailTrace_7028843 : CollatzResearch.WordTrace tailWord_7028843 prefixEnd_7028843 3609174903990348353137445 := by
  unfold tailWord_7028843
  simp only [CollatzResearch.WordTrace]
  refine ⟨256362965274709716658331183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170908643516473144438887455 256362965274709716658331183)
  ·
    refine ⟨384544447912064574987496775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256362965274709716658331183 384544447912064574987496775)
    ·
      refine ⟨576816671868096862481245163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384544447912064574987496775 576816671868096862481245163)
      ·
        refine ⟨865225007802145293721867745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576816671868096862481245163 865225007802145293721867745)
        ·
          refine ⟨648918755851608970291400809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 865225007802145293721867745 648918755851608970291400809)
          ·
            refine ⟨486689066888706727718550607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 648918755851608970291400809 486689066888706727718550607)
            ·
              refine ⟨730033600333060091577825911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486689066888706727718550607 730033600333060091577825911)
              ·
                refine ⟨1095050400499590137366738867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 730033600333060091577825911 1095050400499590137366738867)
                ·
                  refine ⟨1642575600749385206050108301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1095050400499590137366738867 1642575600749385206050108301)
                  ·
                    refine ⟨615965850281019452268790613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1642575600749385206050108301 615965850281019452268790613)
                    ·
                      refine ⟨3609174903990348353137445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 615965850281019452268790613 3609174903990348353137445)
                      ·
                        rfl

theorem cell23_7028843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 9].length) (baseStart_7028843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028843 prefixEnd_7028843 := by exact prefixLift 7028843
  have htrace : WordTrace (prefixWord ++ tailWord_7028843) baseStart_7028843 baseEnd_7028843 := by
    simpa [prefixWord, tailWord_7028843, baseEnd_7028843] using wordTrace_append hprefix tailTrace_7028843
  have hstable : (prefixWord ++ tailWord_7028843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028843).length < 2 ^ (prefixWord ++ tailWord_7028843).sum := by decide
  have hdescent : baseEnd_7028843 < baseStart_7028843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028850 : List Nat := [3, 2, 1, 2, 2, 2, 1, 2, 8]
def baseStart_7028850 : Nat := 118140960795 + 7028850 * 2 ^ 59
def prefixEnd_7028850 : Nat := 4983230072969 + 3 ^ 40 * 7028850 * 2
def baseEnd_7028850 : Nat := 401019833150547758416657

theorem tailTrace_7028850 : CollatzResearch.WordTrace tailWord_7028850 prefixEnd_7028850 401019833150547758416657 := by
  unfold tailWord_7028850
  simp only [CollatzResearch.WordTrace]
  refine ⟨64090805146421089213459001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170908813723789571235890669 64090805146421089213459001)
  ·
    refine ⟨48068103859815816910094251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64090805146421089213459001 48068103859815816910094251)
    ·
      refine ⟨72102155789723725365141377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48068103859815816910094251 72102155789723725365141377)
      ·
        refine ⟨54076616842292794023856033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72102155789723725365141377 54076616842292794023856033)
        ·
          refine ⟨40557462631719595517892025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54076616842292794023856033 40557462631719595517892025)
          ·
            refine ⟨30418096973789696638419019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40557462631719595517892025 30418096973789696638419019)
            ·
              refine ⟨45627145460684544957628529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30418096973789696638419019 45627145460684544957628529)
              ·
                refine ⟨34220359095513408718221397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45627145460684544957628529 34220359095513408718221397)
                ·
                  refine ⟨401019833150547758416657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34220359095513408718221397 401019833150547758416657)
                  ·
                    rfl

theorem cell23_7028850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_7028850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028850 prefixEnd_7028850 := by exact prefixLift 7028850
  have htrace : WordTrace (prefixWord ++ tailWord_7028850) baseStart_7028850 baseEnd_7028850 := by
    simpa [prefixWord, tailWord_7028850, baseEnd_7028850] using wordTrace_append hprefix tailTrace_7028850
  have hstable : (prefixWord ++ tailWord_7028850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028850).length < 2 ^ (prefixWord ++ tailWord_7028850).sum := by decide
  have hdescent : baseEnd_7028850 < baseStart_7028850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028880 : List Nat := [2, 1, 1, 1, 1, 1, 6, 2, 3, 5]
def baseStart_7028880 : Nat := 118140960795 + 7028880 * 2 ^ 59
def prefixEnd_7028880 : Nat := 4983230072969 + 3 ^ 40 * 7028880 * 2
def baseEnd_7028880 : Nat := 1203064634258188236124925

theorem tailTrace_7028880 : CollatzResearch.WordTrace tailWord_7028880 prefixEnd_7028880 1203064634258188236124925 := by
  unfold tailWord_7028880
  simp only [CollatzResearch.WordTrace]
  refine ⟨128182157387787835988714047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170909543183717114651618729 128182157387787835988714047)
  ·
    refine ⟨192273236081681753983071071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128182157387787835988714047 192273236081681753983071071)
    ·
      refine ⟨288409854122522630974606607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192273236081681753983071071 288409854122522630974606607)
      ·
        refine ⟨432614781183783946461909911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288409854122522630974606607 432614781183783946461909911)
        ·
          refine ⟨648922171775675919692864867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432614781183783946461909911 648922171775675919692864867)
          ·
            refine ⟨973383257663513879539297301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648922171775675919692864867 973383257663513879539297301)
            ·
              refine ⟨45627340202977213103404561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 973383257663513879539297301 45627340202977213103404561)
              ·
                refine ⟨34220505152232909827553421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45627340202977213103404561 34220505152232909827553421)
                ·
                  refine ⟨12832689432087341185332533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34220505152232909827553421 12832689432087341185332533)
                  ·
                    refine ⟨1203064634258188236124925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12832689432087341185332533 1203064634258188236124925)
                    ·
                      rfl

theorem cell23_7028880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 3, 5].length) (baseStart_7028880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028880 prefixEnd_7028880 := by exact prefixLift 7028880
  have htrace : WordTrace (prefixWord ++ tailWord_7028880) baseStart_7028880 baseEnd_7028880 := by
    simpa [prefixWord, tailWord_7028880, baseEnd_7028880] using wordTrace_append hprefix tailTrace_7028880
  have hstable : (prefixWord ++ tailWord_7028880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028880).length < 2 ^ (prefixWord ++ tailWord_7028880).sum := by decide
  have hdescent : baseEnd_7028880 < baseStart_7028880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028897 : List Nat := [1, 2, 3, 3, 1, 3, 1, 1, 3, 5]
def baseStart_7028897 : Nat := 118140960795 + 7028897 * 2 ^ 59
def prefixEnd_7028897 : Nat := 4983230072969 + 3 ^ 40 * 7028897 * 2
def baseEnd_7028897 : Nat := 1203067543981897047287399

theorem tailTrace_7028897 : CollatzResearch.WordTrace tailWord_7028897 prefixEnd_7028897 1203067543981897047287399 := by
  unfold tailWord_7028897
  simp only [CollatzResearch.WordTrace]
  refine ⟨256364934816514083880796945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170909956544342722587197963 256364934816514083880796945)
  ·
    refine ⟨192273701112385562910597709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256364934816514083880796945 192273701112385562910597709)
    ·
      refine ⟨72102637917144586091474141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192273701112385562910597709 72102637917144586091474141)
      ·
        refine ⟨27038489218929219784302803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72102637917144586091474141 27038489218929219784302803)
        ·
          refine ⟨40557733828393829676454205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27038489218929219784302803 40557733828393829676454205)
          ·
            refine ⟨15209150185647686128670327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40557733828393829676454205 15209150185647686128670327)
            ·
              refine ⟨22813725278471529193005491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15209150185647686128670327 22813725278471529193005491)
              ·
                refine ⟨34220587917707293789508237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22813725278471529193005491 34220587917707293789508237)
                ·
                  refine ⟨12832720469140235171065589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34220587917707293789508237 12832720469140235171065589)
                  ·
                    refine ⟨1203067543981897047287399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12832720469140235171065589 1203067543981897047287399)
                    ·
                      rfl

theorem cell23_7028897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_7028897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028897 prefixEnd_7028897 := by exact prefixLift 7028897
  have htrace : WordTrace (prefixWord ++ tailWord_7028897) baseStart_7028897 baseEnd_7028897 := by
    simpa [prefixWord, tailWord_7028897, baseEnd_7028897] using wordTrace_append hprefix tailTrace_7028897
  have hstable : (prefixWord ++ tailWord_7028897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028897).length < 2 ^ (prefixWord ++ tailWord_7028897).sum := by decide
  have hdescent : baseEnd_7028897 < baseStart_7028897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028914 : List Nat := [3, 2, 1, 1, 1, 3, 5, 1, 1, 5]
def baseStart_7028914 : Nat := 118140960795 + 7028914 * 2 ^ 59
def prefixEnd_7028914 : Nat := 4983230072969 + 3 ^ 40 * 7028914 * 2
def baseEnd_7028914 : Nat := 1203070453705605858449873

theorem tailTrace_7028914 : CollatzResearch.WordTrace tailWord_7028914 prefixEnd_7028914 1203070453705605858449873 := by
  unfold tailWord_7028914
  simp only [CollatzResearch.WordTrace]
  refine ⟨64091388714363123946041449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170910369904968330522777197 64091388714363123946041449)
  ·
    refine ⟨48068541535772342959531087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64091388714363123946041449 48068541535772342959531087)
    ·
      refine ⟨72102812303658514439296631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48068541535772342959531087 72102812303658514439296631)
      ·
        refine ⟨108154218455487771658944947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72102812303658514439296631 108154218455487771658944947)
        ·
          refine ⟨162231327683231657488417421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108154218455487771658944947 162231327683231657488417421)
          ·
            refine ⟨60836747881211871558156533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162231327683231657488417421 60836747881211871558156533)
            ·
              refine ⟨5703445113863612958577175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60836747881211871558156533 5703445113863612958577175)
              ·
                refine ⟨8555167670795419437865763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5703445113863612958577175 8555167670795419437865763)
                ·
                  refine ⟨12832751506193129156798645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8555167670795419437865763 12832751506193129156798645)
                  ·
                    refine ⟨1203070453705605858449873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12832751506193129156798645 1203070453705605858449873)
                    ·
                      rfl

theorem cell23_7028914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_7028914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028914 prefixEnd_7028914 := by exact prefixLift 7028914
  have htrace : WordTrace (prefixWord ++ tailWord_7028914) baseStart_7028914 baseEnd_7028914 := by
    simpa [prefixWord, tailWord_7028914, baseEnd_7028914] using wordTrace_append hprefix tailTrace_7028914
  have hstable : (prefixWord ++ tailWord_7028914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028914).length < 2 ^ (prefixWord ++ tailWord_7028914).sum := by decide
  have hdescent : baseEnd_7028914 < baseStart_7028914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028928 : List Nat := [2, 1, 1, 2, 5, 1, 4, 2, 1, 1, 3]
def baseStart_7028928 : Nat := 118140960795 + 7028928 * 2 ^ 59
def prefixEnd_7028928 : Nat := 4983230072969 + 3 ^ 40 * 7028928 * 2
def baseEnd_7028928 : Nat := 3609218549845980520574555

theorem tailTrace_7028928 : CollatzResearch.WordTrace tailWord_7028928 prefixEnd_7028928 3609218549845980520574555 := by
  unfold tailWord_7028928
  simp only [CollatzResearch.WordTrace]
  refine ⟨128183032739700888087587719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170910710319601184116783625 128183032739700888087587719)
  ·
    refine ⟨192274549109551332131381579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128183032739700888087587719 192274549109551332131381579)
    ·
      refine ⟨288411823664326998197072369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192274549109551332131381579 288411823664326998197072369)
      ·
        refine ⟨216308867748245248647804277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288411823664326998197072369 216308867748245248647804277)
        ·
          refine ⟨20278956351397992060731651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 216308867748245248647804277 20278956351397992060731651)
          ·
            refine ⟨30418434527096988091097477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20278956351397992060731651 30418434527096988091097477)
            ·
              refine ⟨5703456473830685267080777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30418434527096988091097477 5703456473830685267080777)
              ·
                refine ⟨4277592355373013950310583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5703456473830685267080777 4277592355373013950310583)
                ·
                  refine ⟨6416388533059520925465875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4277592355373013950310583 6416388533059520925465875)
                  ·
                    refine ⟨9624582799589281388198813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6416388533059520925465875 9624582799589281388198813)
                    ·
                      refine ⟨3609218549845980520574555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9624582799589281388198813 3609218549845980520574555)
                      ·
                        rfl

theorem cell23_7028928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 1, 1, 3].length) (baseStart_7028928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028928 prefixEnd_7028928 := by exact prefixLift 7028928
  have htrace : WordTrace (prefixWord ++ tailWord_7028928) baseStart_7028928 baseEnd_7028928 := by
    simpa [prefixWord, tailWord_7028928, baseEnd_7028928] using wordTrace_append hprefix tailTrace_7028928
  have hstable : (prefixWord ++ tailWord_7028928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028928).length < 2 ^ (prefixWord ++ tailWord_7028928).sum := by decide
  have hdescent : baseEnd_7028928 < baseStart_7028928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7028968 : List Nat := [2, 1, 4, 1, 2, 2, 1, 5, 1, 2, 2]
def baseStart_7028968 : Nat := 118140960795 + 7028968 * 2 ^ 59
def prefixEnd_7028968 : Nat := 4983230072969 + 3 ^ 40 * 7028968 * 2
def baseEnd_7028968 : Nat := 3609239089072160364074371

theorem tailTrace_7028968 : CollatzResearch.WordTrace tailWord_7028968 prefixEnd_7028968 3609239089072160364074371 := by
  unfold tailWord_7028968
  simp only [CollatzResearch.WordTrace]
  refine ⟨128183762199628431503315779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170911682932837908671087705 128183762199628431503315779)
  ·
    refine ⟨192275643299442647254973669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128183762199628431503315779 192275643299442647254973669)
    ·
      refine ⟨36051683118645496360307563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192275643299442647254973669 36051683118645496360307563)
      ·
        refine ⟨54077524677968244540461345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36051683118645496360307563 54077524677968244540461345)
        ·
          refine ⟨40558143508476183405346009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54077524677968244540461345 40558143508476183405346009)
          ·
            refine ⟨30418607631357137554009507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40558143508476183405346009 30418607631357137554009507)
            ·
              refine ⟨45627911447035706331014261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30418607631357137554009507 45627911447035706331014261)
              ·
                refine ⟨4277616698159597468532587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45627911447035706331014261 4277616698159597468532587)
                ·
                  refine ⟨6416425047239396202798881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4277616698159597468532587 6416425047239396202798881)
                  ·
                    refine ⟨4812318785429547152099161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6416425047239396202798881 4812318785429547152099161)
                    ·
                      refine ⟨3609239089072160364074371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4812318785429547152099161 3609239089072160364074371)
                      ·
                        rfl

theorem cell23_7028968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_7028968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7028968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7028968 prefixEnd_7028968 := by exact prefixLift 7028968
  have htrace : WordTrace (prefixWord ++ tailWord_7028968) baseStart_7028968 baseEnd_7028968 := by
    simpa [prefixWord, tailWord_7028968, baseEnd_7028968] using wordTrace_append hprefix tailTrace_7028968
  have hstable : (prefixWord ++ tailWord_7028968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7028968).length < 2 ^ (prefixWord ++ tailWord_7028968).sum := by decide
  have hdescent : baseEnd_7028968 < baseStart_7028968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7028968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029027 : List Nat := [1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 5]
def baseStart_7029027 : Nat := 118140960795 + 7029027 * 2 ^ 59
def prefixEnd_7029027 : Nat := 4983230072969 + 3 ^ 40 * 7029027 * 2
def baseEnd_7029027 : Nat := 3609269384430775633236599

theorem tailTrace_7029027 : CollatzResearch.WordTrace tailWord_7029027 prefixEnd_7029027 3609269384430775633236599 := by
  unfold tailWord_7029027
  simp only [CollatzResearch.WordTrace]
  refine ⟨256369676306043116083029335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170913117537362077388686223 256369676306043116083029335)
  ·
    refine ⟨384554514459064674124544003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256369676306043116083029335 384554514459064674124544003)
    ·
      refine ⟨576831771688597011186816005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384554514459064674124544003 576831771688597011186816005)
      ·
        refine ⟨108155957191611939597528001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 576831771688597011186816005 108155957191611939597528001)
        ·
          refine ⟨81116967893708954698146001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108155957191611939597528001 81116967893708954698146001)
          ·
            refine ⟨60837725920281716023609501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81116967893708954698146001 60837725920281716023609501)
            ·
              refine ⟨22814147220105643508853563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60837725920281716023609501 22814147220105643508853563)
              ·
                refine ⟨34221220830158465263280345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22814147220105643508853563 34221220830158465263280345)
                ·
                  refine ⟨25665915622618848947460259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34221220830158465263280345 25665915622618848947460259)
                  ·
                    refine ⟨38498873433928273421190389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25665915622618848947460259 38498873433928273421190389)
                    ·
                      refine ⟨3609269384430775633236599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38498873433928273421190389 3609269384430775633236599)
                      ·
                        rfl

theorem cell23_7029027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_7029027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029027 prefixEnd_7029027 := by exact prefixLift 7029027
  have htrace : WordTrace (prefixWord ++ tailWord_7029027) baseStart_7029027 baseEnd_7029027 := by
    simpa [prefixWord, tailWord_7029027, baseEnd_7029027] using wordTrace_append hprefix tailTrace_7029027
  have hstable : (prefixWord ++ tailWord_7029027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029027).length < 2 ^ (prefixWord ++ tailWord_7029027).sum := by decide
  have hdescent : baseEnd_7029027 < baseStart_7029027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029087 : List Nat := [1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 5]
def baseStart_7029087 : Nat := 118140960795 + 7029087 * 2 ^ 59
def prefixEnd_7029087 : Nat := 4983230072969 + 3 ^ 40 * 7029087 * 2
def baseEnd_7029087 : Nat := 3609300193270045398486323

theorem tailTrace_7029087 : CollatzResearch.WordTrace tailWord_7029087 prefixEnd_7029087 3609300193270045398486323 := by
  unfold tailWord_7029087
  simp only [CollatzResearch.WordTrace]
  refine ⟨256371864685825746330213515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170914576457217164220142343 256371864685825746330213515)
  ·
    refine ⟨384557797028738619495320273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256371864685825746330213515 384557797028738619495320273)
    ·
      refine ⟨288418347771553964621490205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384557797028738619495320273 288418347771553964621490205)
      ·
        refine ⟨108156880414332736733058827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288418347771553964621490205 108156880414332736733058827)
        ·
          refine ⟨162235320621499105099588241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108156880414332736733058827 162235320621499105099588241)
          ·
            refine ⟨121676490466124328824691181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162235320621499105099588241 121676490466124328824691181)
            ·
              refine ⟨45628683924796623309259193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121676490466124328824691181 45628683924796623309259193)
              ·
                refine ⟨34221512943597467481944395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45628683924796623309259193 34221512943597467481944395)
                ·
                  refine ⟨51332269415396201222916593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34221512943597467481944395 51332269415396201222916593)
                  ·
                    refine ⟨38499202061547150917187445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51332269415396201222916593 38499202061547150917187445)
                    ·
                      refine ⟨3609300193270045398486323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38499202061547150917187445 3609300193270045398486323)
                      ·
                        rfl

theorem cell23_7029087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_7029087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029087 prefixEnd_7029087 := by exact prefixLift 7029087
  have htrace : WordTrace (prefixWord ++ tailWord_7029087) baseStart_7029087 baseEnd_7029087 := by
    simpa [prefixWord, tailWord_7029087, baseEnd_7029087] using wordTrace_append hprefix tailTrace_7029087
  have hstable : (prefixWord ++ tailWord_7029087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029087).length < 2 ^ (prefixWord ++ tailWord_7029087).sum := by decide
  have hdescent : baseEnd_7029087 < baseStart_7029087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029098 : List Nat := [3, 1, 3, 3, 1, 1, 4, 2, 5]
def baseStart_7029098 : Nat := 118140960795 + 7029098 * 2 ^ 59
def prefixEnd_7029098 : Nat := 4983230072969 + 3 ^ 40 * 7029098 * 2
def baseEnd_7029098 : Nat := 401033982395249428383197

theorem tailTrace_7029098 : CollatzResearch.WordTrace tailWord_7029098 prefixEnd_7029098 401033982395249428383197 := by
  unfold tailWord_7029098
  simp only [CollatzResearch.WordTrace]
  refine ⟨64093066472196473802215987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170914843925857263472575965 64093066472196473802215987)
  ·
    refine ⟨96139599708294710703323981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64093066472196473802215987 96139599708294710703323981)
    ·
      refine ⟨36052349890610516513746493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96139599708294710703323981 36052349890610516513746493)
      ·
        refine ⟨13519631208978943692654935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36052349890610516513746493 13519631208978943692654935)
        ·
          refine ⟨20279446813468415538982403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13519631208978943692654935 20279446813468415538982403)
          ·
            refine ⟨30419170220202623308473605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20279446813468415538982403 30419170220202623308473605)
            ·
              refine ⟨5703594416287991870338801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30419170220202623308473605 5703594416287991870338801)
              ·
                refine ⟨4277695812215993902754101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5703594416287991870338801 4277695812215993902754101)
                ·
                  refine ⟨401033982395249428383197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4277695812215993902754101 401033982395249428383197)
                  ·
                    rfl

theorem cell23_7029098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 5].length) (baseStart_7029098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029098 prefixEnd_7029098 := by exact prefixLift 7029098
  have htrace : WordTrace (prefixWord ++ tailWord_7029098) baseStart_7029098 baseEnd_7029098 := by
    simpa [prefixWord, tailWord_7029098, baseEnd_7029098] using wordTrace_append hprefix tailTrace_7029098
  have hstable : (prefixWord ++ tailWord_7029098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029098).length < 2 ^ (prefixWord ++ tailWord_7029098).sum := by decide
  have hdescent : baseEnd_7029098 < baseStart_7029098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029131 : List Nat := [1, 1, 1, 1, 4, 6, 1, 1, 2, 1, 4]
def baseStart_7029131 : Nat := 118140960795 + 7029131 * 2 ^ 59
def prefixEnd_7029131 : Nat := 4983230072969 + 3 ^ 40 * 7029131 * 2
def baseEnd_7029131 : Nat := 3609322786418843226336121

theorem tailTrace_7029131 : CollatzResearch.WordTrace tailWord_7029131 prefixEnd_7029131 3609322786418843226336121 := by
  unfold tailWord_7029131
  simp only [CollatzResearch.WordTrace]
  refine ⟨256373469497666341844815247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170915646331777561229876831 256373469497666341844815247)
  ·
    refine ⟨384560204246499512767222871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256373469497666341844815247 384560204246499512767222871)
    ·
      refine ⟨576840306369749269150834307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384560204246499512767222871 576840306369749269150834307)
      ·
        refine ⟨865260459554623903726251461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576840306369749269150834307 865260459554623903726251461)
        ·
          refine ⟨162236336166491981948672149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 865260459554623903726251461 162236336166491981948672149)
          ·
            refine ⟨7604828257804311653844007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 162236336166491981948672149 7604828257804311653844007)
            ·
              refine ⟨11407242386706467480766011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7604828257804311653844007 11407242386706467480766011)
              ·
                refine ⟨17110863580059701221149017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11407242386706467480766011 17110863580059701221149017)
                ·
                  refine ⟨12833147685044775915861763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17110863580059701221149017 12833147685044775915861763)
                  ·
                    refine ⟨19249721527567163873792645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12833147685044775915861763 19249721527567163873792645)
                    ·
                      refine ⟨3609322786418843226336121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19249721527567163873792645 3609322786418843226336121)
                      ·
                        rfl

theorem cell23_7029131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 1, 4].length) (baseStart_7029131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029131 prefixEnd_7029131 := by exact prefixLift 7029131
  have htrace : WordTrace (prefixWord ++ tailWord_7029131) baseStart_7029131 baseEnd_7029131 := by
    simpa [prefixWord, tailWord_7029131, baseEnd_7029131] using wordTrace_append hprefix tailTrace_7029131
  have hstable : (prefixWord ++ tailWord_7029131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029131).length < 2 ^ (prefixWord ++ tailWord_7029131).sum := by decide
  have hdescent : baseEnd_7029131 < baseStart_7029131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029144 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 2, 1, 6]
def baseStart_7029144 : Nat := 118140960795 + 7029144 * 2 ^ 59
def prefixEnd_7029144 : Nat := 4983230072969 + 3 ^ 40 * 7029144 * 2
def baseEnd_7029144 : Nat := 3609329461667351675473561

theorem tailTrace_7029144 : CollatzResearch.WordTrace tailWord_7029144 prefixEnd_7029144 3609329461667351675473561 := by
  unfold tailWord_7029144
  simp only [CollatzResearch.WordTrace]
  refine ⟨128186971823309622532519243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170915962431079496710025657 128186971823309622532519243)
  ·
    refine ⟨192280457734964433798778865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128186971823309622532519243 192280457734964433798778865)
    ·
      refine ⟨144210343301223325349084149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192280457734964433798778865 144210343301223325349084149)
      ·
        refine ⟨13519719684489686751476639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144210343301223325349084149 13519719684489686751476639)
        ·
          refine ⟨20279579526734530127214959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13519719684489686751476639 20279579526734530127214959)
          ·
            refine ⟨30419369290101795190822439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20279579526734530127214959 30419369290101795190822439)
            ·
              refine ⟨45629053935152692786233659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30419369290101795190822439 45629053935152692786233659)
              ·
                refine ⟨68443580902729039179350489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45629053935152692786233659 68443580902729039179350489)
                ·
                  refine ⟨51332685677046779384512867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68443580902729039179350489 51332685677046779384512867)
                  ·
                    refine ⟨76999028515570169076769301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51332685677046779384512867 76999028515570169076769301)
                    ·
                      refine ⟨3609329461667351675473561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76999028515570169076769301 3609329461667351675473561)
                      ·
                        rfl

theorem cell23_7029144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_7029144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029144 prefixEnd_7029144 := by exact prefixLift 7029144
  have htrace : WordTrace (prefixWord ++ tailWord_7029144) baseStart_7029144 baseEnd_7029144 := by
    simpa [prefixWord, tailWord_7029144, baseEnd_7029144] using wordTrace_append hprefix tailTrace_7029144
  have hstable : (prefixWord ++ tailWord_7029144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029144).length < 2 ^ (prefixWord ++ tailWord_7029144).sum := by decide
  have hdescent : baseEnd_7029144 < baseStart_7029144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029154 : List Nat := [3, 3, 1, 2, 1, 1, 3, 1, 8]
def baseStart_7029154 : Nat := 118140960795 + 7029154 * 2 ^ 59
def prefixEnd_7029154 : Nat := 4983230072969 + 3 ^ 40 * 7029154 * 2
def baseEnd_7029154 : Nat := 401037177385988515149835

theorem tailTrace_7029154 : CollatzResearch.WordTrace tailWord_7029154 prefixEnd_7029154 401037177385988515149835 := by
  unfold tailWord_7029154
  simp only [CollatzResearch.WordTrace]
  refine ⟨64093577094145754193225629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170916205584388677848601677 64093577094145754193225629)
  ·
    refine ⟨24035091410304657822459611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64093577094145754193225629 24035091410304657822459611)
    ·
      refine ⟨36052637115456986733689417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24035091410304657822459611 36052637115456986733689417)
      ·
        refine ⟨27039477836592740050267063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36052637115456986733689417 27039477836592740050267063)
        ·
          refine ⟨40559216754889110075400595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27039477836592740050267063 40559216754889110075400595)
          ·
            refine ⟨60838825132333665113100893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40559216754889110075400595 60838825132333665113100893)
            ·
              refine ⟨22814559424625124417412835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60838825132333665113100893 22814559424625124417412835)
              ·
                refine ⟨34221839136937686626119253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22814559424625124417412835 34221839136937686626119253)
                ·
                  refine ⟨401037177385988515149835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34221839136937686626119253 401037177385988515149835)
                  ·
                    rfl

theorem cell23_7029154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_7029154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029154 prefixEnd_7029154 := by exact prefixLift 7029154
  have htrace : WordTrace (prefixWord ++ tailWord_7029154) baseStart_7029154 baseEnd_7029154 := by
    simpa [prefixWord, tailWord_7029154, baseEnd_7029154] using wordTrace_append hprefix tailTrace_7029154
  have hstable : (prefixWord ++ tailWord_7029154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029154).length < 2 ^ (prefixWord ++ tailWord_7029154).sum := by decide
  have hdescent : baseEnd_7029154 < baseStart_7029154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029157 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 1, 1, 8]
def baseStart_7029157 : Nat := 118140960795 + 7029157 * 2 ^ 59
def prefixEnd_7029157 : Nat := 4983230072969 + 3 ^ 40 * 7029157 * 2
def baseEnd_7029157 : Nat := 3609336136915860124611001

theorem tailTrace_7029157 : CollatzResearch.WordTrace tailWord_7029157 prefixEnd_7029157 3609336136915860124611001 := by
  unfold tailWord_7029157
  simp only [CollatzResearch.WordTrace]
  refine ⟨256374417795572148285261725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170916278530381432190174483 256374417795572148285261725)
  ·
    refine ⟨96140406673339555606973147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256374417795572148285261725 96140406673339555606973147)
    ·
      refine ⟨144210610010009333410459721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96140406673339555606973147 144210610010009333410459721)
      ·
        refine ⟨108157957507507000057844791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144210610010009333410459721 108157957507507000057844791)
        ·
          refine ⟨162236936261260500086767187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108157957507507000057844791 162236936261260500086767187)
          ·
            refine ⟨243355404391890750130150781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162236936261260500086767187 243355404391890750130150781)
            ·
              refine ⟨91258276646959031298806543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243355404391890750130150781 91258276646959031298806543)
              ·
                refine ⟨136887414970438546948209815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91258276646959031298806543 136887414970438546948209815)
                ·
                  refine ⟨205331122455657820422314723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136887414970438546948209815 205331122455657820422314723)
                  ·
                    refine ⟨307996683683486730633472085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 205331122455657820422314723 307996683683486730633472085)
                    ·
                      refine ⟨3609336136915860124611001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 307996683683486730633472085 3609336136915860124611001)
                      ·
                        rfl

theorem cell23_7029157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_7029157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029157 prefixEnd_7029157 := by exact prefixLift 7029157
  have htrace : WordTrace (prefixWord ++ tailWord_7029157) baseStart_7029157 baseEnd_7029157 := by
    simpa [prefixWord, tailWord_7029157, baseEnd_7029157] using wordTrace_append hprefix tailTrace_7029157
  have hstable : (prefixWord ++ tailWord_7029157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029157).length < 2 ^ (prefixWord ++ tailWord_7029157).sum := by decide
  have hdescent : baseEnd_7029157 < baseStart_7029157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029191 : List Nat := [1, 1, 4, 1, 1, 4, 2, 1, 1, 5, 2]
def baseStart_7029191 : Nat := 118140960795 + 7029191 * 2 ^ 59
def prefixEnd_7029191 : Nat := 4983230072969 + 3 ^ 40 * 7029191 * 2
def baseEnd_7029191 : Nat := 3609353595258112991585845

theorem tailTrace_7029191 : CollatzResearch.WordTrace tailWord_7029191 prefixEnd_7029191 3609353595258112991585845 := by
  unfold tailWord_7029191
  simp only [CollatzResearch.WordTrace]
  refine ⟨256375657877448972091999427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170917105251632648061332951 256375657877448972091999427)
  ·
    refine ⟨384563486816173458137999141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256375657877448972091999427 384563486816173458137999141)
    ·
      refine ⟨72105653778032523400874839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 384563486816173458137999141 72105653778032523400874839)
      ·
        refine ⟨108158480667048785101312259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72105653778032523400874839 108158480667048785101312259)
        ·
          refine ⟨162237721000573177651968389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108158480667048785101312259 162237721000573177651968389)
          ·
            refine ⟨30419572687607470809744073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162237721000573177651968389 30419572687607470809744073)
            ·
              refine ⟨22814679515705603107308055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30419572687607470809744073 22814679515705603107308055)
              ·
                refine ⟨34222019273558404660962083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22814679515705603107308055 34222019273558404660962083)
                ·
                  refine ⟨51333028910337606991443125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34222019273558404660962083 51333028910337606991443125)
                  ·
                    refine ⟨4812471460344150655447793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51333028910337606991443125 4812471460344150655447793)
                    ·
                      refine ⟨3609353595258112991585845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4812471460344150655447793 3609353595258112991585845)
                      ·
                        rfl

theorem cell23_7029191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 5, 2].length) (baseStart_7029191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029191 prefixEnd_7029191 := by exact prefixLift 7029191
  have htrace : WordTrace (prefixWord ++ tailWord_7029191) baseStart_7029191 baseEnd_7029191 := by
    simpa [prefixWord, tailWord_7029191, baseEnd_7029191] using wordTrace_append hprefix tailTrace_7029191
  have hstable : (prefixWord ++ tailWord_7029191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029191).length < 2 ^ (prefixWord ++ tailWord_7029191).sum := by decide
  have hdescent : baseEnd_7029191 < baseStart_7029191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029255 : List Nat := [1, 1, 4, 3, 3, 1, 3, 1, 1, 1, 4]
def baseStart_7029255 : Nat := 118140960795 + 7029255 * 2 ^ 59
def prefixEnd_7029255 : Nat := 4983230072969 + 3 ^ 40 * 7029255 * 2
def baseEnd_7029255 : Nat := 3609386458020000741185551

theorem tailTrace_7029255 : CollatzResearch.WordTrace tailWord_7029255 prefixEnd_7029255 3609386458020000741185551 := by
  unfold tailWord_7029255
  simp only [CollatzResearch.WordTrace]
  refine ⟨256377992149217111022329219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170918661432811407348219479 256377992149217111022329219)
  ·
    refine ⟨384566988223825666533493829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256377992149217111022329219 384566988223825666533493829)
    ·
      refine ⟨72106310291967312475030093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 384566988223825666533493829 72106310291967312475030093)
      ·
        refine ⟨27039866359487742178136285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72106310291967312475030093 27039866359487742178136285)
        ·
          refine ⟨10139949884807903316801107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27039866359487742178136285 10139949884807903316801107)
          ·
            refine ⟨15209924827211854975201661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10139949884807903316801107 15209924827211854975201661)
            ·
              refine ⟨5703721810204445615700623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15209924827211854975201661 5703721810204445615700623)
              ·
                refine ⟨8555582715306668423550935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5703721810204445615700623 8555582715306668423550935)
                ·
                  refine ⟨12833374072960002635326403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8555582715306668423550935 12833374072960002635326403)
                  ·
                    refine ⟨19250061109440003952989605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12833374072960002635326403 19250061109440003952989605)
                    ·
                      refine ⟨3609386458020000741185551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19250061109440003952989605 3609386458020000741185551)
                      ·
                        rfl

theorem cell23_7029255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_7029255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029255 prefixEnd_7029255 := by exact prefixLift 7029255
  have htrace : WordTrace (prefixWord ++ tailWord_7029255) baseStart_7029255 baseEnd_7029255 := by
    simpa [prefixWord, tailWord_7029255, baseEnd_7029255] using wordTrace_append hprefix tailTrace_7029255
  have hstable : (prefixWord ++ tailWord_7029255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029255).length < 2 ^ (prefixWord ++ tailWord_7029255).sum := by decide
  have hdescent : baseEnd_7029255 < baseStart_7029255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029272 : List Nat := [2, 1, 2, 3, 3, 2, 1, 4, 1, 2, 2]
def baseStart_7029272 : Nat := 118140960795 + 7029272 * 2 ^ 59
def prefixEnd_7029272 : Nat := 4983230072969 + 3 ^ 40 * 7029272 * 2
def baseEnd_7029272 : Nat := 3609395187191127174672973

theorem tailTrace_7029272 : CollatzResearch.WordTrace tailWord_7029272 prefixEnd_7029272 3609395187191127174672973 := by
  unfold tailWord_7029272
  simp only [CollatzResearch.WordTrace]
  refine ⟨128189306095077761462849035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170919074793437015283798713 128189306095077761462849035)
  ·
    refine ⟨192283959142616642194273553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128189306095077761462849035 192283959142616642194273553)
    ·
      refine ⟨144212969356962481645705165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192283959142616642194273553 144212969356962481645705165)
      ·
        refine ⟨54079863508860930617139437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144212969356962481645705165 54079863508860930617139437)
        ·
          refine ⟨20279948815822848981427289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54079863508860930617139437 20279948815822848981427289)
          ·
            refine ⟨15209961611867136736070467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20279948815822848981427289 15209961611867136736070467)
            ·
              refine ⟨22814942417800705104105701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15209961611867136736070467 22814942417800705104105701)
              ·
                refine ⟨4277801703337632207019819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22814942417800705104105701 4277801703337632207019819)
                ·
                  refine ⟨6416702555006448310529729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4277801703337632207019819 6416702555006448310529729)
                  ·
                    refine ⟨4812526916254836232897297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6416702555006448310529729 4812526916254836232897297)
                    ·
                      refine ⟨3609395187191127174672973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4812526916254836232897297 3609395187191127174672973)
                      ·
                        rfl

theorem cell23_7029272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_7029272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029272 prefixEnd_7029272 := by exact prefixLift 7029272
  have htrace : WordTrace (prefixWord ++ tailWord_7029272) baseStart_7029272 baseEnd_7029272 := by
    simpa [prefixWord, tailWord_7029272, baseEnd_7029272] using wordTrace_append hprefix tailTrace_7029272
  have hstable : (prefixWord ++ tailWord_7029272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029272).length < 2 ^ (prefixWord ++ tailWord_7029272).sum := by decide
  have hdescent : baseEnd_7029272 < baseStart_7029272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029274 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 2, 7]
def baseStart_7029274 : Nat := 118140960795 + 7029274 * 2 ^ 59
def prefixEnd_7029274 : Nat := 4983230072969 + 3 ^ 40 * 7029274 * 2
def baseEnd_7029274 : Nat := 1203132071384145388949321

theorem tailTrace_7029274 : CollatzResearch.WordTrace tailWord_7029274 prefixEnd_7029274 1203132071384145388949321 := by
  unfold tailWord_7029274
  simp only [CollatzResearch.WordTrace]
  refine ⟨64094671284037069316817719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170919123424098851511513917 64094671284037069316817719)
  ·
    refine ⟨96142006926055603975226579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64094671284037069316817719 96142006926055603975226579)
    ·
      refine ⟨144213010389083405962839869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96142006926055603975226579 144213010389083405962839869)
      ·
        refine ⟨54079878895906277236064951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144213010389083405962839869 54079878895906277236064951)
        ·
          refine ⟨81119818343859415854097427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54079878895906277236064951 81119818343859415854097427)
          ·
            refine ⟨121679727515789123781146141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81119818343859415854097427 121679727515789123781146141)
            ·
              refine ⟨45629897818420921417929803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121679727515789123781146141 45629897818420921417929803)
              ·
                refine ⟨68444846727631382126894705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45629897818420921417929803 68444846727631382126894705)
                ·
                  refine ⟨51333635045723536595171029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68444846727631382126894705 51333635045723536595171029)
                  ·
                    refine ⟨1203132071384145388949321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51333635045723536595171029 1203132071384145388949321)
                    ·
                      rfl

theorem cell23_7029274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_7029274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029274 prefixEnd_7029274 := by exact prefixLift 7029274
  have htrace : WordTrace (prefixWord ++ tailWord_7029274) baseStart_7029274 baseEnd_7029274 := by
    simpa [prefixWord, tailWord_7029274, baseEnd_7029274] using wordTrace_append hprefix tailTrace_7029274
  have hstable : (prefixWord ++ tailWord_7029274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029274).length < 2 ^ (prefixWord ++ tailWord_7029274).sum := by decide
  have hdescent : baseEnd_7029274 < baseStart_7029274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029288 : List Nat := [2, 1, 5, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_7029288 : Nat := 118140960795 + 7029288 * 2 ^ 59
def prefixEnd_7029288 : Nat := 4983230072969 + 3 ^ 40 * 7029288 * 2
def baseEnd_7029288 : Nat := 3609403402881599112072899

theorem tailTrace_7029288 : CollatzResearch.WordTrace tailWord_7029288 prefixEnd_7029288 3609403402881599112072899 := by
  unfold tailWord_7029288
  simp only [CollatzResearch.WordTrace]
  refine ⟨128189597879048778829140259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170919463838731705105520345 128189597879048778829140259)
  ·
    refine ⟨192284396818573168243710389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128189597879048778829140259 192284396818573168243710389)
    ·
      refine ⟨18026662201741234522847849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 192284396818573168243710389 18026662201741234522847849)
      ·
        refine ⟨13519996651305925892135887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18026662201741234522847849 13519996651305925892135887)
        ·
          refine ⟨20279994976958888838203831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13519996651305925892135887 20279994976958888838203831)
          ·
            refine ⟨30419992465438333257305747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20279994976958888838203831 30419992465438333257305747)
            ·
              refine ⟨45629988698157499885958621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30419992465438333257305747 45629988698157499885958621)
              ·
                refine ⟨17111245761809062457234483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45629988698157499885958621 17111245761809062457234483)
                ·
                  refine ⟨25666868642713593685851725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17111245761809062457234483 25666868642713593685851725)
                  ·
                    refine ⟨9625075741017597632194397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25666868642713593685851725 9625075741017597632194397)
                    ·
                      refine ⟨3609403402881599112072899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9625075741017597632194397 3609403402881599112072899)
                      ·
                        rfl

theorem cell23_7029288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_7029288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029288 prefixEnd_7029288 := by exact prefixLift 7029288
  have htrace : WordTrace (prefixWord ++ tailWord_7029288) baseStart_7029288 baseEnd_7029288 := by
    simpa [prefixWord, tailWord_7029288, baseEnd_7029288] using wordTrace_append hprefix tailTrace_7029288
  have hstable : (prefixWord ++ tailWord_7029288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029288).length < 2 ^ (prefixWord ++ tailWord_7029288).sum := by decide
  have hdescent : baseEnd_7029288 < baseStart_7029288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029298 : List Nat := [3, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2]
def baseStart_7029298 : Nat := 118140960795 + 7029298 * 2 ^ 59
def prefixEnd_7029298 : Nat := 4983230072969 + 3 ^ 40 * 7029298 * 2
def baseEnd_7029298 : Nat := 3609408537688144072947853

theorem tailTrace_7029298 : CollatzResearch.WordTrace tailWord_7029298 prefixEnd_7029298 3609408537688144072947853 := by
  unfold tailWord_7029298
  simp only [CollatzResearch.WordTrace]
  refine ⟨64094890122015332341536137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170919706992040886244096365 64094890122015332341536137)
  ·
    refine ⟨48071167591511499256152103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64094890122015332341536137 48071167591511499256152103)
    ·
      refine ⟨72106751387267248884228155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48071167591511499256152103 72106751387267248884228155)
      ·
        refine ⟨108160127080900873326342233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72106751387267248884228155 108160127080900873326342233)
        ·
          refine ⟨81120095310675654994756675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108160127080900873326342233 81120095310675654994756675)
          ·
            refine ⟨121680142966013482492135013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81120095310675654994756675 121680142966013482492135013)
            ·
              refine ⟨22815026806127527967275315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121680142966013482492135013 22815026806127527967275315)
              ·
                refine ⟨34222540209191291950912973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22815026806127527967275315 34222540209191291950912973)
                ·
                  refine ⟨12833452578446734481592365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34222540209191291950912973 12833452578446734481592365)
                  ·
                    refine ⟨4812544716917525430597137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12833452578446734481592365 4812544716917525430597137)
                    ·
                      refine ⟨3609408537688144072947853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4812544716917525430597137 3609408537688144072947853)
                      ·
                        rfl

theorem cell23_7029298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2].length) (baseStart_7029298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029298 prefixEnd_7029298 := by exact prefixLift 7029298
  have htrace : WordTrace (prefixWord ++ tailWord_7029298) baseStart_7029298 baseEnd_7029298 := by
    simpa [prefixWord, tailWord_7029298, baseEnd_7029298] using wordTrace_append hprefix tailTrace_7029298
  have hstable : (prefixWord ++ tailWord_7029298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029298).length < 2 ^ (prefixWord ++ tailWord_7029298).sum := by decide
  have hdescent : baseEnd_7029298 < baseStart_7029298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029304 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 1, 8]
def baseStart_7029304 : Nat := 118140960795 + 7029304 * 2 ^ 59
def prefixEnd_7029304 : Nat := 4983230072969 + 3 ^ 40 * 7029304 * 2
def baseEnd_7029304 : Nat := 1203137206190690349824275

theorem tailTrace_7029304 : CollatzResearch.WordTrace tailWord_7029304 prefixEnd_7029304 1203137206190690349824275 := by
  unfold tailWord_7029304
  simp only [CollatzResearch.WordTrace]
  refine ⟨128189889663019796195431483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170919852884026394927241977 128189889663019796195431483)
  ·
    refine ⟨192284834494529694293147225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128189889663019796195431483 192284834494529694293147225)
    ·
      refine ⟨144213625870897270719860419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192284834494529694293147225 144213625870897270719860419)
      ·
        refine ⟨216320438806345906079790629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144213625870897270719860419 216320438806345906079790629)
        ·
          refine ⟨40560082276189857389960743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216320438806345906079790629 40560082276189857389960743)
          ·
            refine ⟨60840123414284786084941115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40560082276189857389960743 60840123414284786084941115)
            ·
              refine ⟨91260185121427179127411673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60840123414284786084941115 91260185121427179127411673)
              ·
                refine ⟨68445138841070384345558755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91260185121427179127411673 68445138841070384345558755)
                ·
                  refine ⟨102667708261605576518338133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68445138841070384345558755 102667708261605576518338133)
                  ·
                    refine ⟨1203137206190690349824275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102667708261605576518338133 1203137206190690349824275)
                    ·
                      rfl

theorem cell23_7029304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_7029304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029304 prefixEnd_7029304 := by exact prefixLift 7029304
  have htrace : WordTrace (prefixWord ++ tailWord_7029304) baseStart_7029304 baseEnd_7029304 := by
    simpa [prefixWord, tailWord_7029304, baseEnd_7029304] using wordTrace_append hprefix tailTrace_7029304
  have hstable : (prefixWord ++ tailWord_7029304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029304).length < 2 ^ (prefixWord ++ tailWord_7029304).sum := by decide
  have hdescent : baseEnd_7029304 < baseStart_7029304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029316 : List Nat := [2, 3, 5, 1, 2, 1, 1, 2, 2, 4]
def baseStart_7029316 : Nat := 118140960795 + 7029316 * 2 ^ 59
def prefixEnd_7029316 : Nat := 4983230072969 + 3 ^ 40 * 7029316 * 2
def baseEnd_7029316 : Nat := 1203139260113308334174257

theorem tailTrace_7029316 : CollatzResearch.WordTrace tailWord_7029316 prefixEnd_7029316 1203139260113308334174257 := by
  unfold tailWord_7029316
  simp only [CollatzResearch.WordTrace]
  refine ⟨128190108500998059220149901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170920144667997412293533201 128190108500998059220149901)
  ·
    refine ⟨48071290687874272207556213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128190108500998059220149901 48071290687874272207556213)
    ·
      refine ⟨4506683501988213019458395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48071290687874272207556213 4506683501988213019458395)
      ·
        refine ⟨6760025252982319529187593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4506683501988213019458395 6760025252982319529187593)
        ·
          refine ⟨5070018939736739646890695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6760025252982319529187593 5070018939736739646890695)
          ·
            refine ⟨7605028409605109470336043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5070018939736739646890695 7605028409605109470336043)
            ·
              refine ⟨11407542614407664205504065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7605028409605109470336043 11407542614407664205504065)
              ·
                refine ⟨8555656960805748154128049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11407542614407664205504065 8555656960805748154128049)
                ·
                  refine ⟨6416742720604311115596037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8555656960805748154128049 6416742720604311115596037)
                  ·
                    refine ⟨1203139260113308334174257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6416742720604311115596037 1203139260113308334174257)
                    ·
                      rfl

theorem cell23_7029316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_7029316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029316 prefixEnd_7029316 := by exact prefixLift 7029316
  have htrace : WordTrace (prefixWord ++ tailWord_7029316) baseStart_7029316 baseEnd_7029316 := by
    simpa [prefixWord, tailWord_7029316, baseEnd_7029316] using wordTrace_append hprefix tailTrace_7029316
  have hstable : (prefixWord ++ tailWord_7029316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029316).length < 2 ^ (prefixWord ++ tailWord_7029316).sum := by decide
  have hdescent : baseEnd_7029316 < baseStart_7029316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029345 : List Nat := [1, 2, 3, 1, 1, 6, 1, 1, 1, 4, 2]
def baseStart_7029345 : Nat := 118140960795 + 7029345 * 2 ^ 59
def prefixEnd_7029345 : Nat := 4983230072969 + 3 ^ 40 * 7029345 * 2
def baseEnd_7029345 : Nat := 3609432671278905389060137

theorem tailTrace_7029345 : CollatzResearch.WordTrace tailWord_7029345 prefixEnd_7029345 3609432671278905389060137 := by
  unfold tailWord_7029345
  simp only [CollatzResearch.WordTrace]
  refine ⟨256381274718891056393105489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170920849812594037595403659 256381274718891056393105489)
  ·
    refine ⟨192285956039168292294829117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256381274718891056393105489 192285956039168292294829117)
    ·
      refine ⟨72107233514688109610560919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192285956039168292294829117 72107233514688109610560919)
      ·
        refine ⟨108160850272032164415841379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72107233514688109610560919 108160850272032164415841379)
        ·
          refine ⟨162241275408048246623762069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108160850272032164415841379 162241275408048246623762069)
          ·
            refine ⟨7605059784752261560488847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 162241275408048246623762069 7605059784752261560488847)
            ·
              refine ⟨11407589677128392340733271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7605059784752261560488847 11407589677128392340733271)
              ·
                refine ⟨17111384515692588511099907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11407589677128392340733271 17111384515692588511099907)
                ·
                  refine ⟨25667076773538882766649861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17111384515692588511099907 25667076773538882766649861)
                  ·
                    refine ⟨4812576895038540518746849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25667076773538882766649861 4812576895038540518746849)
                    ·
                      refine ⟨3609432671278905389060137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4812576895038540518746849 3609432671278905389060137)
                      ·
                        rfl

theorem cell23_7029345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 4, 2].length) (baseStart_7029345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029345 prefixEnd_7029345 := by exact prefixLift 7029345
  have htrace : WordTrace (prefixWord ++ tailWord_7029345) baseStart_7029345 baseEnd_7029345 := by
    simpa [prefixWord, tailWord_7029345, baseEnd_7029345] using wordTrace_append hprefix tailTrace_7029345
  have hstable : (prefixWord ++ tailWord_7029345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029345).length < 2 ^ (prefixWord ++ tailWord_7029345).sum := by decide
  have hdescent : baseEnd_7029345 < baseStart_7029345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029381 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 4, 5]
def baseStart_7029381 : Nat := 118140960795 + 7029381 * 2 ^ 59
def prefixEnd_7029381 : Nat := 4983230072969 + 3 ^ 40 * 7029381 * 2
def baseEnd_7029381 : Nat := 1203150385527489082736657

theorem tailTrace_7029381 : CollatzResearch.WordTrace tailWord_7029381 prefixEnd_7029381 1203150385527489082736657 := by
  unfold tailWord_7029381
  simp only [CollatzResearch.WordTrace]
  refine ⟨256382587746760634541415997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170921725164507089694277331 256382587746760634541415997)
  ·
    refine ⟨96143470405035237953030999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256382587746760634541415997 96143470405035237953030999)
    ·
      refine ⟨144215205607552856929546499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96143470405035237953030999 144215205607552856929546499)
      ·
        refine ⟨216322808411329285394319749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144215205607552856929546499 216322808411329285394319749)
        ·
          refine ⟨40560526577124241011434953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216322808411329285394319749 40560526577124241011434953)
          ·
            refine ⟨30420394932843180758576215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40560526577124241011434953 30420394932843180758576215)
            ·
              refine ⟨45630592399264771137864323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30420394932843180758576215 45630592399264771137864323)
              ·
                refine ⟨68445888598897156706796485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45630592399264771137864323 68445888598897156706796485)
                ·
                  refine ⟨12833604112293216882524341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68445888598897156706796485 12833604112293216882524341)
                  ·
                    refine ⟨1203150385527489082736657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12833604112293216882524341 1203150385527489082736657)
                    ·
                      rfl

theorem cell23_7029381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 5].length) (baseStart_7029381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029381 prefixEnd_7029381 := by exact prefixLift 7029381
  have htrace : WordTrace (prefixWord ++ tailWord_7029381) baseStart_7029381 baseEnd_7029381 := by
    simpa [prefixWord, tailWord_7029381, baseEnd_7029381] using wordTrace_append hprefix tailTrace_7029381
  have hstable : (prefixWord ++ tailWord_7029381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029381).length < 2 ^ (prefixWord ++ tailWord_7029381).sum := by decide
  have hdescent : baseEnd_7029381 < baseStart_7029381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029396 : List Nat := [2, 4, 2, 2, 1, 3, 2, 1, 2, 2, 2]
def baseStart_7029396 : Nat := 118140960795 + 7029396 * 2 ^ 59
def prefixEnd_7029396 : Nat := 4983230072969 + 3 ^ 40 * 7029396 * 2
def baseEnd_7029396 : Nat := 3609458858792284689522403

theorem tailTrace_7029396 : CollatzResearch.WordTrace tailWord_7029396 prefixEnd_7029396 3609458858792284689522403 := by
  unfold tailWord_7029396
  simp only [CollatzResearch.WordTrace]
  refine ⟨128191567420853146051606021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170922089894470861402141361 128191567420853146051606021)
  ·
    refine ⟨24035918891409964884676129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128191567420853146051606021 24035918891409964884676129)
    ·
      refine ⟨18026939168557473663507097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24035918891409964884676129 18026939168557473663507097)
      ·
        refine ⟨13520204376418105247630323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18026939168557473663507097 13520204376418105247630323)
        ·
          refine ⟨20280306564627157871445485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13520204376418105247630323 20280306564627157871445485)
          ·
            refine ⟨7605114961735184201792057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20280306564627157871445485 7605114961735184201792057)
            ·
              refine ⟨5703836221301388151344043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7605114961735184201792057 5703836221301388151344043)
              ·
                refine ⟨8555754331952082227016065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5703836221301388151344043 8555754331952082227016065)
                ·
                  refine ⟨6416815748964061670262049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8555754331952082227016065 6416815748964061670262049)
                  ·
                    refine ⟨4812611811723046252696537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6416815748964061670262049 4812611811723046252696537)
                    ·
                      refine ⟨3609458858792284689522403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4812611811723046252696537 3609458858792284689522403)
                      ·
                        rfl

theorem cell23_7029396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_7029396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029396 prefixEnd_7029396 := by exact prefixLift 7029396
  have htrace : WordTrace (prefixWord ++ tailWord_7029396) baseStart_7029396 baseEnd_7029396 := by
    simpa [prefixWord, tailWord_7029396, baseEnd_7029396] using wordTrace_append hprefix tailTrace_7029396
  have hstable : (prefixWord ++ tailWord_7029396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029396).length < 2 ^ (prefixWord ++ tailWord_7029396).sum := by decide
  have hdescent : baseEnd_7029396 < baseStart_7029396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029401 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 4, 1, 4]
def baseStart_7029401 : Nat := 118140960795 + 7029401 * 2 ^ 59
def prefixEnd_7029401 : Nat := 4983230072969 + 3 ^ 40 * 7029401 * 2
def baseEnd_7029401 : Nat := 3609461426195557169959879

theorem tailTrace_7029401 : CollatzResearch.WordTrace tailWord_7029401 prefixEnd_7029401 3609461426195557169959879 := by
  unfold tailWord_7029401
  simp only [CollatzResearch.WordTrace]
  refine ⟨256383317206688177957144057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170922211471125451971429371 256383317206688177957144057)
  ·
    refine ⟨192287487905016133467858043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256383317206688177957144057 192287487905016133467858043)
    ·
      refine ⟨288431231857524200201787065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192287487905016133467858043 288431231857524200201787065)
      ·
        refine ⟨216323423893143150151340299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288431231857524200201787065 216323423893143150151340299)
        ·
          refine ⟨324485135839714725227010449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216323423893143150151340299 324485135839714725227010449)
          ·
            refine ⟨243363851879786043920257837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324485135839714725227010449 243363851879786043920257837)
            ·
              refine ⟨91261444454919766470096689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243363851879786043920257837 91261444454919766470096689)
              ·
                refine ⟨68446083341189824852572517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91261444454919766470096689 68446083341189824852572517)
                ·
                  refine ⟨12833640626473092159857347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68446083341189824852572517 12833640626473092159857347)
                  ·
                    refine ⟨19250460939709638239786021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12833640626473092159857347 19250460939709638239786021)
                    ·
                      refine ⟨3609461426195557169959879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19250460939709638239786021 3609461426195557169959879)
                      ·
                        rfl

theorem cell23_7029401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_7029401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029401 prefixEnd_7029401 := by exact prefixLift 7029401
  have htrace : WordTrace (prefixWord ++ tailWord_7029401) baseStart_7029401 baseEnd_7029401 := by
    simpa [prefixWord, tailWord_7029401, baseEnd_7029401] using wordTrace_append hprefix tailTrace_7029401
  have hstable : (prefixWord ++ tailWord_7029401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029401).length < 2 ^ (prefixWord ++ tailWord_7029401).sum := by decide
  have hdescent : baseEnd_7029401 < baseStart_7029401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029451 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 3]
def baseStart_7029451 : Nat := 118140960795 + 7029451 * 2 ^ 59
def prefixEnd_7029451 : Nat := 4983230072969 + 3 ^ 40 * 7029451 * 2
def baseEnd_7029451 : Nat := 3609487100228281974334649

theorem tailTrace_7029451 : CollatzResearch.WordTrace tailWord_7029451 prefixEnd_7029451 3609487100228281974334649 := by
  unfold tailWord_7029451
  simp only [CollatzResearch.WordTrace]
  refine ⟨256385140856507036496464207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170923427237671357664309471 256385140856507036496464207)
  ·
    refine ⟨384577711284760554744696311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256385140856507036496464207 384577711284760554744696311)
    ·
      refine ⟨576866566927140832117044467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384577711284760554744696311 576866566927140832117044467)
      ·
        refine ⟨865299850390711248175566701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576866566927140832117044467 865299850390711248175566701)
        ·
          refine ⟨324487443896516718065837513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 865299850390711248175566701 324487443896516718065837513)
          ·
            refine ⟨243365582922387538549378135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324487443896516718065837513 243365582922387538549378135)
            ·
              refine ⟨365048374383581307824067203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243365582922387538549378135 365048374383581307824067203)
              ·
                refine ⟨547572561575371961736100805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365048374383581307824067203 547572561575371961736100805)
                ·
                  refine ⟨102669855295382242825518901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 547572561575371961736100805 102669855295382242825518901)
                  ·
                    refine ⟨9625298933942085264892397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102669855295382242825518901 9625298933942085264892397)
                    ·
                      refine ⟨3609487100228281974334649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9625298933942085264892397 3609487100228281974334649)
                      ·
                        rfl

theorem cell23_7029451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 3].length) (baseStart_7029451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029451 prefixEnd_7029451 := by exact prefixLift 7029451
  have htrace : WordTrace (prefixWord ++ tailWord_7029451) baseStart_7029451 baseEnd_7029451 := by
    simpa [prefixWord, tailWord_7029451, baseEnd_7029451] using wordTrace_append hprefix tailTrace_7029451
  have hstable : (prefixWord ++ tailWord_7029451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029451).length < 2 ^ (prefixWord ++ tailWord_7029451).sum := by decide
  have hdescent : baseEnd_7029451 < baseStart_7029451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029485 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 5, 1, 3]
def baseStart_7029485 : Nat := 118140960795 + 7029485 * 2 ^ 59
def prefixEnd_7029485 : Nat := 4983230072969 + 3 ^ 40 * 7029485 * 2
def baseEnd_7029485 : Nat := 3609504558570534841309493

theorem tailTrace_7029485 : CollatzResearch.WordTrace tailWord_7029485 prefixEnd_7029485 3609504558570534841309493 := by
  unfold tailWord_7029485
  simp only [CollatzResearch.WordTrace]
  refine ⟨256386380938383860303201909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170924253958922573535467939 256386380938383860303201909)
  ·
    refine ⟨24036223212973486903425179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 256386380938383860303201909 24036223212973486903425179)
    ·
      refine ⟨36054334819460230355137769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24036223212973486903425179 36054334819460230355137769)
      ·
        refine ⟨27040751114595172766353327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36054334819460230355137769 27040751114595172766353327)
        ·
          refine ⟨40561126671892759149529991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27040751114595172766353327 40561126671892759149529991)
          ·
            refine ⟨60841690007839138724294987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40561126671892759149529991 60841690007839138724294987)
            ·
              refine ⟨91262535011758708086442481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60841690007839138724294987 91262535011758708086442481)
              ·
                refine ⟨68446901258819031064831861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91262535011758708086442481 68446901258819031064831861)
                ·
                  refine ⟨6416896993014284162327987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68446901258819031064831861 6416896993014284162327987)
                  ·
                    refine ⟨9625345489521426243491981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6416896993014284162327987 9625345489521426243491981)
                    ·
                      refine ⟨3609504558570534841309493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9625345489521426243491981 3609504558570534841309493)
                      ·
                        rfl

theorem cell23_7029485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_7029485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029485 prefixEnd_7029485 := by exact prefixLift 7029485
  have htrace : WordTrace (prefixWord ++ tailWord_7029485) baseStart_7029485 baseEnd_7029485 := by
    simpa [prefixWord, tailWord_7029485, baseEnd_7029485] using wordTrace_append hprefix tailTrace_7029485
  have hstable : (prefixWord ++ tailWord_7029485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029485).length < 2 ^ (prefixWord ++ tailWord_7029485).sum := by decide
  have hdescent : baseEnd_7029485 < baseStart_7029485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029488 : List Nat := [2, 1, 1, 1, 3, 1, 5, 3, 1, 5]
def baseStart_7029488 : Nat := 118140960795 + 7029488 * 2 ^ 59
def prefixEnd_7029488 : Nat := 4983230072969 + 3 ^ 40 * 7029488 * 2
def baseEnd_7029488 : Nat := 1203168699670832776523993

theorem tailTrace_7029488 : CollatzResearch.WordTrace tailWord_7029488 prefixEnd_7029488 1203168699670832776523993 := by
  unfold tailWord_7029488
  simp only [CollatzResearch.WordTrace]
  refine ⟨128193245178686495907780559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170924326904915327877040745 128193245178686495907780559)
  ·
    refine ⟨192289867768029743861670839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128193245178686495907780559 192289867768029743861670839)
    ·
      refine ⟨288434801652044615792506259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192289867768029743861670839 288434801652044615792506259)
      ·
        refine ⟨432652202478066923688759389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288434801652044615792506259 432652202478066923688759389)
        ·
          refine ⟨162244575929275096383284771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 432652202478066923688759389 162244575929275096383284771)
          ·
            refine ⟨243366863893912644574927157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162244575929275096383284771 243366863893912644574927157)
            ·
              refine ⟨22815643490054310428899421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 243366863893912644574927157 22815643490054310428899421)
              ·
                refine ⟨8555866308770366410837283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22815643490054310428899421 8555866308770366410837283)
                ·
                  refine ⟨12833799463155549616255925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8555866308770366410837283 12833799463155549616255925)
                  ·
                    refine ⟨1203168699670832776523993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12833799463155549616255925 1203168699670832776523993)
                    ·
                      rfl

theorem cell23_7029488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 1, 5].length) (baseStart_7029488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029488 prefixEnd_7029488 := by exact prefixLift 7029488
  have htrace : WordTrace (prefixWord ++ tailWord_7029488) baseStart_7029488 baseEnd_7029488 := by
    simpa [prefixWord, tailWord_7029488, baseEnd_7029488] using wordTrace_append hprefix tailTrace_7029488
  have hstable : (prefixWord ++ tailWord_7029488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029488).length < 2 ^ (prefixWord ++ tailWord_7029488).sum := by decide
  have hdescent : baseEnd_7029488 < baseStart_7029488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029492 : List Nat := [2, 6, 1, 1, 2, 1, 1, 1, 8]
def baseStart_7029492 : Nat := 118140960795 + 7029492 * 2 ^ 59
def prefixEnd_7029492 : Nat := 4983230072969 + 3 ^ 40 * 7029492 * 2
def baseEnd_7029492 : Nat := 401056461437235145991329

theorem tailTrace_7029492 : CollatzResearch.WordTrace tailWord_7029492 prefixEnd_7029492 401056461437235145991329 := by
  unfold tailWord_7029492
  simp only [CollatzResearch.WordTrace]
  refine ⟨128193318124679250249353365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170924424166239000332471153 128193318124679250249353365)
  ·
    refine ⟨6009061787094339855438439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 128193318124679250249353365 6009061787094339855438439)
    ·
      refine ⟨9013592680641509783157659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6009061787094339855438439 9013592680641509783157659)
      ·
        refine ⟨13520389020962264674736489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9013592680641509783157659 13520389020962264674736489)
        ·
          refine ⟨10140291765721698506052367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13520389020962264674736489 10140291765721698506052367)
          ·
            refine ⟨15210437648582547759078551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10140291765721698506052367 15210437648582547759078551)
            ·
              refine ⟨22815656472873821638617827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15210437648582547759078551 22815656472873821638617827)
              ·
                refine ⟨34223484709310732457926741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22815656472873821638617827 34223484709310732457926741)
                ·
                  refine ⟨401056461437235145991329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34223484709310732457926741 401056461437235145991329)
                  ·
                    rfl

theorem cell23_7029492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_7029492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029492 prefixEnd_7029492 := by exact prefixLift 7029492
  have htrace : WordTrace (prefixWord ++ tailWord_7029492) baseStart_7029492 baseEnd_7029492 := by
    simpa [prefixWord, tailWord_7029492, baseEnd_7029492] using wordTrace_append hprefix tailTrace_7029492
  have hstable : (prefixWord ++ tailWord_7029492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029492).length < 2 ^ (prefixWord ++ tailWord_7029492).sum := by decide
  have hdescent : baseEnd_7029492 < baseStart_7029492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029502 : List Nat := [4, 2, 2, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_7029502 : Nat := 118140960795 + 7029502 * 2 ^ 59
def prefixEnd_7029502 : Nat := 4983230072969 + 3 ^ 40 * 7029502 * 2
def baseEnd_7029502 : Nat := 3609513287741661274796915

theorem tailTrace_7029502 : CollatzResearch.WordTrace tailWord_7029502 prefixEnd_7029502 3609513287741661274796915 := by
  unfold tailWord_7029502
  simp only [CollatzResearch.WordTrace]
  refine ⟨32048375122415284025821345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170924667319548181471047173 32048375122415284025821345)
  ·
    refine ⟨24036281341811463019366009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32048375122415284025821345 24036281341811463019366009)
    ·
      refine ⟨18027211006358597264524507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24036281341811463019366009 18027211006358597264524507)
      ·
        refine ⟨27040816509537895896786761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18027211006358597264524507 27040816509537895896786761)
        ·
          refine ⟨20280612382153421922590071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27040816509537895896786761 20280612382153421922590071)
          ·
            refine ⟨30420918573230132883885107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20280612382153421922590071 30420918573230132883885107)
            ·
              refine ⟨45631377859845199325827661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30420918573230132883885107 45631377859845199325827661)
              ·
                refine ⟨17111766697441949747185373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45631377859845199325827661 17111766697441949747185373)
                ·
                  refine ⟨6416912511540731155194515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17111766697441949747185373 6416912511540731155194515)
                  ·
                    refine ⟨9625368767311096732791773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6416912511540731155194515 9625368767311096732791773)
                    ·
                      refine ⟨3609513287741661274796915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9625368767311096732791773 3609513287741661274796915)
                      ·
                        rfl

theorem cell23_7029502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_7029502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029502 prefixEnd_7029502 := by exact prefixLift 7029502
  have htrace : WordTrace (prefixWord ++ tailWord_7029502) baseStart_7029502 baseEnd_7029502 := by
    simpa [prefixWord, tailWord_7029502, baseEnd_7029502] using wordTrace_append hprefix tailTrace_7029502
  have hstable : (prefixWord ++ tailWord_7029502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029502).length < 2 ^ (prefixWord ++ tailWord_7029502).sum := by decide
  have hdescent : baseEnd_7029502 < baseStart_7029502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029525 : List Nat := [1, 3, 2, 1, 2, 2, 4, 2, 1, 1, 4]
def baseStart_7029525 : Nat := 118140960795 + 7029525 * 2 ^ 59
def prefixEnd_7029525 : Nat := 4983230072969 + 3 ^ 40 * 7029525 * 2
def baseEnd_7029525 : Nat := 3609525097796714684809309

theorem tailTrace_7029525 : CollatzResearch.WordTrace tailWord_7029525 prefixEnd_7029525 3609525097796714684809309 := by
  unfold tailWord_7029525
  simp only [CollatzResearch.WordTrace]
  refine ⟨256387839858238947134658029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170925226572159298089772019 256387839858238947134658029)
  ·
    refine ⟨96145439946839605175496761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256387839858238947134658029 96145439946839605175496761)
    ·
      refine ⟨72109079960129703881622571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96145439946839605175496761 72109079960129703881622571)
      ·
        refine ⟨108163619940194555822433857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72109079960129703881622571 108163619940194555822433857)
        ·
          refine ⟨81122714955145916866825393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108163619940194555822433857 81122714955145916866825393)
          ·
            refine ⟨60842036216359437650119045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81122714955145916866825393 60842036216359437650119045)
            ·
              refine ⟨11407881790567394559397321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60842036216359437650119045 11407881790567394559397321)
              ·
                refine ⟨8555911342925545919547991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11407881790567394559397321 8555911342925545919547991)
                ·
                  refine ⟨12833867014388318879321987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8555911342925545919547991 12833867014388318879321987)
                  ·
                    refine ⟨19250800521582478318982981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12833867014388318879321987 19250800521582478318982981)
                    ·
                      refine ⟨3609525097796714684809309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19250800521582478318982981 3609525097796714684809309)
                      ·
                        rfl

theorem cell23_7029525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_7029525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029525 prefixEnd_7029525 := by exact prefixLift 7029525
  have htrace : WordTrace (prefixWord ++ tailWord_7029525) baseStart_7029525 baseEnd_7029525 := by
    simpa [prefixWord, tailWord_7029525, baseEnd_7029525] using wordTrace_append hprefix tailTrace_7029525
  have hstable : (prefixWord ++ tailWord_7029525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029525).length < 2 ^ (prefixWord ++ tailWord_7029525).sum := by decide
  have hdescent : baseEnd_7029525 < baseStart_7029525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029551 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 6]
def baseStart_7029551 : Nat := 118140960795 + 7029551 * 2 ^ 59
def prefixEnd_7029551 : Nat := 4983230072969 + 3 ^ 40 * 7029551 * 2
def baseEnd_7029551 : Nat := 3609538448293731583084189

theorem tailTrace_7029551 : CollatzResearch.WordTrace tailWord_7029551 prefixEnd_7029551 3609538448293731583084189 := by
  unfold tailWord_7029551
  simp only [CollatzResearch.WordTrace]
  refine ⟨256388788156144753575104507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170925858770763169050069671 256388788156144753575104507)
  ·
    refine ⟨384583182234217130362656761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256388788156144753575104507 384583182234217130362656761)
    ·
      refine ⟨288437386675662847771992571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384583182234217130362656761 288437386675662847771992571)
      ·
        refine ⟨432656080013494271657988857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288437386675662847771992571 432656080013494271657988857)
        ·
          refine ⟨324492060010120703743491643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 432656080013494271657988857 324492060010120703743491643)
          ·
            refine ⟨486738090015181055615237465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324492060010120703743491643 486738090015181055615237465)
            ·
              refine ⟨365053567511385791711428099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 486738090015181055615237465 365053567511385791711428099)
              ·
                refine ⟨547580351267078687567142149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365053567511385791711428099 547580351267078687567142149)
                ·
                  refine ⟨102671315862577253918839153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 547580351267078687567142149 102671315862577253918839153)
                  ·
                    refine ⟨77003486896932940439129365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102671315862577253918839153 77003486896932940439129365)
                    ·
                      refine ⟨3609538448293731583084189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77003486896932940439129365 3609538448293731583084189)
                      ·
                        rfl

theorem cell23_7029551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_7029551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029551 prefixEnd_7029551 := by exact prefixLift 7029551
  have htrace : WordTrace (prefixWord ++ tailWord_7029551) baseStart_7029551 baseEnd_7029551 := by
    simpa [prefixWord, tailWord_7029551, baseEnd_7029551] using wordTrace_append hprefix tailTrace_7029551
  have hstable : (prefixWord ++ tailWord_7029551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029551).length < 2 ^ (prefixWord ++ tailWord_7029551).sum := by decide
  have hdescent : baseEnd_7029551 < baseStart_7029551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029565 : List Nat := [1, 4, 1, 4, 2, 1, 2, 8]
def baseStart_7029565 : Nat := 118140960795 + 7029565 * 2 ^ 59
def prefixEnd_7029565 : Nat := 4983230072969 + 3 ^ 40 * 7029565 * 2
def baseEnd_7029565 : Nat := 133686875445292389937375

theorem tailTrace_7029565 : CollatzResearch.WordTrace tailWord_7029565 prefixEnd_7029565 133686875445292389937375 := by
  unfold tailWord_7029565
  simp only [CollatzResearch.WordTrace]
  refine ⟨256389298778094033966114149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170926199185396022644076099 256389298778094033966114149)
  ·
    refine ⟨48072993520892631368646403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256389298778094033966114149 48072993520892631368646403)
    ·
      refine ⟨72109490281338947052969605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48072993520892631368646403 72109490281338947052969605)
      ·
        refine ⟨13520529427751052572431801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72109490281338947052969605 13520529427751052572431801)
        ·
          refine ⟨10140397070813289429323851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13520529427751052572431801 10140397070813289429323851)
          ·
            refine ⟨15210595606219934143985777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10140397070813289429323851 15210595606219934143985777)
            ·
              refine ⟨11407946704664950607989333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15210595606219934143985777 11407946704664950607989333)
              ·
                refine ⟨133686875445292389937375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11407946704664950607989333 133686875445292389937375)
                ·
                  rfl

theorem cell23_7029565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 8].length) (baseStart_7029565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029565 prefixEnd_7029565 := by exact prefixLift 7029565
  have htrace : WordTrace (prefixWord ++ tailWord_7029565) baseStart_7029565 baseEnd_7029565 := by
    simpa [prefixWord, tailWord_7029565, baseEnd_7029565] using wordTrace_append hprefix tailTrace_7029565
  have hstable : (prefixWord ++ tailWord_7029565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029565).length < 2 ^ (prefixWord ++ tailWord_7029565).sum := by decide
  have hdescent : baseEnd_7029565 < baseStart_7029565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029569 : List Nat := [1, 2, 5, 3, 1, 1, 1, 3, 2, 4]
def baseStart_7029569 : Nat := 118140960795 + 7029569 * 2 ^ 59
def prefixEnd_7029569 : Nat := 4983230072969 + 3 ^ 40 * 7029569 * 2
def baseEnd_7029569 : Nat := 1203182563648504170886369

theorem tailTrace_7029569 : CollatzResearch.WordTrace tailWord_7029569 prefixEnd_7029569 1203182563648504170886369 := by
  unfold tailWord_7029569
  simp only [CollatzResearch.WordTrace]
  refine ⟨256389444670079542649259761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170926296446719695099506507 256389444670079542649259761)
  ·
    refine ⟨192292083502559656986944821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256389444670079542649259761 192292083502559656986944821)
    ·
      refine ⟨18027382828364967842526077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 192292083502559656986944821 18027382828364967842526077)
      ·
        refine ⟨6760268560636862940947279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18027382828364967842526077 6760268560636862940947279)
        ·
          refine ⟨10140402840955294411420919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6760268560636862940947279 10140402840955294411420919)
          ·
            refine ⟨15210604261432941617131379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10140402840955294411420919 15210604261432941617131379)
            ·
              refine ⟨22815906392149412425697069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15210604261432941617131379 22815906392149412425697069)
              ·
                refine ⟨8555964897056029659636401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22815906392149412425697069 8555964897056029659636401)
                ·
                  refine ⟨6416973672792022244727301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8555964897056029659636401 6416973672792022244727301)
                  ·
                    refine ⟨1203182563648504170886369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6416973672792022244727301 1203182563648504170886369)
                    ·
                      rfl

theorem cell23_7029569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_7029569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029569 prefixEnd_7029569 := by exact prefixLift 7029569
  have htrace : WordTrace (prefixWord ++ tailWord_7029569) baseStart_7029569 baseEnd_7029569 := by
    simpa [prefixWord, tailWord_7029569, baseEnd_7029569] using wordTrace_append hprefix tailTrace_7029569
  have hstable : (prefixWord ++ tailWord_7029569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029569).length < 2 ^ (prefixWord ++ tailWord_7029569).sum := by decide
  have hdescent : baseEnd_7029569 < baseStart_7029569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029618 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 1, 3, 5]
def baseStart_7029618 : Nat := 118140960795 + 7029618 * 2 ^ 59
def prefixEnd_7029618 : Nat := 4983230072969 + 3 ^ 40 * 7029618 * 2
def baseEnd_7029618 : Nat := 3609572851497582820946381

theorem tailTrace_7029618 : CollatzResearch.WordTrace tailWord_7029618 prefixEnd_7029618 3609572851497582820946381 := by
  unfold tailWord_7029618
  simp only [CollatzResearch.WordTrace]
  refine ⟨64097807961725506004448377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170927487897934682678529005 64097807961725506004448377)
  ·
    refine ⟨48073355971294129503336283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64097807961725506004448377 48073355971294129503336283)
    ·
      refine ⟨72110033956941194255004425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48073355971294129503336283 72110033956941194255004425)
      ·
        refine ⟨54082525467705895691253319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72110033956941194255004425 54082525467705895691253319)
        ·
          refine ⟨81123788201558843536879979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54082525467705895691253319 81123788201558843536879979)
          ·
            refine ⟨121685682302338265305319969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81123788201558843536879979 121685682302338265305319969)
            ·
              refine ⟨91264261726753698978989977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121685682302338265305319969 91264261726753698978989977)
              ·
                refine ⟨68448196295065274234242483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91264261726753698978989977 68448196295065274234242483)
                ·
                  refine ⟨102672294442597911351363725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68448196295065274234242483 102672294442597911351363725)
                  ·
                    refine ⟨38502110415974216756761397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102672294442597911351363725 38502110415974216756761397)
                    ·
                      refine ⟨3609572851497582820946381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38502110415974216756761397 3609572851497582820946381)
                      ·
                        rfl

theorem cell23_7029618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_7029618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029618 prefixEnd_7029618 := by exact prefixLift 7029618
  have htrace : WordTrace (prefixWord ++ tailWord_7029618) baseStart_7029618 baseEnd_7029618 := by
    simpa [prefixWord, tailWord_7029618, baseEnd_7029618] using wordTrace_append hprefix tailTrace_7029618
  have hstable : (prefixWord ++ tailWord_7029618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029618).length < 2 ^ (prefixWord ++ tailWord_7029618).sum := by decide
  have hdescent : baseEnd_7029618 < baseStart_7029618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029666 : List Nat := [3, 3, 1, 2, 2, 1, 3, 2, 2, 2, 2]
def baseStart_7029666 : Nat := 118140960795 + 7029666 * 2 ^ 59
def prefixEnd_7029666 : Nat := 4983230072969 + 3 ^ 40 * 7029666 * 2
def baseEnd_7029666 : Nat := 3609597498568998633146161

theorem tailTrace_7029666 : CollatzResearch.WordTrace tailWord_7029666 prefixEnd_7029666 3609597498568998633146161 := by
  unfold tailWord_7029666
  simp only [CollatzResearch.WordTrace]
  refine ⟨64098245637682032053885213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170928655033818752143693901 64098245637682032053885213)
  ·
    refine ⟨24036842114130762020206955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64098245637682032053885213 24036842114130762020206955)
    ·
      refine ⟨36055263171196143030310433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24036842114130762020206955 36055263171196143030310433)
      ·
        refine ⟨27041447378397107272732825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36055263171196143030310433 27041447378397107272732825)
        ·
          refine ⟨20281085533797830454549619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27041447378397107272732825 20281085533797830454549619)
          ·
            refine ⟨30421628300696745681824429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20281085533797830454549619 30421628300696745681824429)
            ·
              refine ⟨11408110612761279630684161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30421628300696745681824429 11408110612761279630684161)
              ·
                refine ⟨8556082959570959723013121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11408110612761279630684161 8556082959570959723013121)
                ·
                  refine ⟨6417062219678219792259841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8556082959570959723013121 6417062219678219792259841)
                  ·
                    refine ⟨4812796664758664844194881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6417062219678219792259841 4812796664758664844194881)
                    ·
                      refine ⟨3609597498568998633146161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4812796664758664844194881 3609597498568998633146161)
                      ·
                        rfl

theorem cell23_7029666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_7029666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029666 prefixEnd_7029666 := by exact prefixLift 7029666
  have htrace : WordTrace (prefixWord ++ tailWord_7029666) baseStart_7029666 baseEnd_7029666 := by
    simpa [prefixWord, tailWord_7029666, baseEnd_7029666] using wordTrace_append hprefix tailTrace_7029666
  have hstable : (prefixWord ++ tailWord_7029666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029666).length < 2 ^ (prefixWord ++ tailWord_7029666).sum := by decide
  have hdescent : baseEnd_7029666 < baseStart_7029666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029722 : List Nat := [3, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4]
def baseStart_7029722 : Nat := 118140960795 + 7029722 * 2 ^ 59
def prefixEnd_7029722 : Nat := 4983230072969 + 3 ^ 40 * 7029722 * 2
def baseEnd_7029722 : Nat := 3609626253485650414045903

theorem tailTrace_7029722 : CollatzResearch.WordTrace tailWord_7029722 prefixEnd_7029722 3609626253485650414045903 := by
  unfold tailWord_7029722
  simp only [CollatzResearch.WordTrace]
  refine ⟨64098756259631312444894855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170930016692350166519719613 64098756259631312444894855)
  ·
    refine ⟨96148134389446968667342283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64098756259631312444894855 96148134389446968667342283)
    ·
      refine ⟨144222201584170453001013425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96148134389446968667342283 144222201584170453001013425)
      ·
        refine ⟨108166651188127839750760069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144222201584170453001013425 108166651188127839750760069)
        ·
          refine ⟨20281247097773969953267513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108166651188127839750760069 20281247097773969953267513)
          ·
            refine ⟨15210935323330477464950635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20281247097773969953267513 15210935323330477464950635)
            ·
              refine ⟨22816402984995716197425953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15210935323330477464950635 22816402984995716197425953)
              ·
                refine ⟨17112302238746787148069465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22816402984995716197425953 17112302238746787148069465)
                ·
                  refine ⟨12834226679060090361052099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17112302238746787148069465 12834226679060090361052099)
                  ·
                    refine ⟨19251340018590135541578149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12834226679060090361052099 19251340018590135541578149)
                    ·
                      refine ⟨3609626253485650414045903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19251340018590135541578149 3609626253485650414045903)
                      ·
                        rfl

theorem cell23_7029722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_7029722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029722 prefixEnd_7029722 := by exact prefixLift 7029722
  have htrace : WordTrace (prefixWord ++ tailWord_7029722) baseStart_7029722 baseEnd_7029722 := by
    simpa [prefixWord, tailWord_7029722, baseEnd_7029722] using wordTrace_append hprefix tailTrace_7029722
  have hstable : (prefixWord ++ tailWord_7029722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029722).length < 2 ^ (prefixWord ++ tailWord_7029722).sum := by decide
  have hdescent : baseEnd_7029722 < baseStart_7029722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029783 : List Nat := [1, 1, 3, 5, 1, 3, 2, 2, 1, 4]
def baseStart_7029783 : Nat := 118140960795 + 7029783 * 2 ^ 59
def prefixEnd_7029783 : Nat := 4983230072969 + 3 ^ 40 * 7029783 * 2
def baseEnd_7029783 : Nat := 1203219191935191558461041

theorem tailTrace_7029783 : CollatzResearch.WordTrace tailWord_7029783 prefixEnd_7029783 1203219191935191558461041 := by
  unfold tailWord_7029783
  simp only [CollatzResearch.WordTrace]
  refine ⟨256397249891304257197550003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170931499927536171465033335 256397249891304257197550003)
  ·
    refine ⟨384595874836956385796325005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256397249891304257197550003 384595874836956385796325005)
    ·
      refine ⟨144223453063858644673621877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384595874836956385796325005 144223453063858644673621877)
      ·
        refine ⟨13520948724736747938152051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144223453063858644673621877 13520948724736747938152051)
        ·
          refine ⟨20281423087105121907228077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13520948724736747938152051 20281423087105121907228077)
          ·
            refine ⟨7605533657664420715210529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20281423087105121907228077 7605533657664420715210529)
            ·
              refine ⟨5704150243248315536407897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7605533657664420715210529 5704150243248315536407897)
              ·
                refine ⟨4278112682436236652305923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5704150243248315536407897 4278112682436236652305923)
                ·
                  refine ⟨6417169023654354978458885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4278112682436236652305923 6417169023654354978458885)
                  ·
                    refine ⟨1203219191935191558461041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6417169023654354978458885 1203219191935191558461041)
                    ·
                      rfl

theorem cell23_7029783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 1, 4].length) (baseStart_7029783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029783 prefixEnd_7029783 := by exact prefixLift 7029783
  have htrace : WordTrace (prefixWord ++ tailWord_7029783) baseStart_7029783 baseEnd_7029783 := by
    simpa [prefixWord, tailWord_7029783, baseEnd_7029783] using wordTrace_append hprefix tailTrace_7029783
  have hstable : (prefixWord ++ tailWord_7029783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029783).length < 2 ^ (prefixWord ++ tailWord_7029783).sum := by decide
  have hdescent : baseEnd_7029783 < baseStart_7029783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029816 : List Nat := [2, 1, 2, 1, 5, 3, 1, 1, 2, 3, 2]
def baseStart_7029816 : Nat := 118140960795 + 7029816 * 2 ^ 59
def prefixEnd_7029816 : Nat := 4983230072969 + 3 ^ 40 * 7029816 * 2
def baseEnd_7029816 : Nat := 3609674520667173046270471

theorem tailTrace_7029816 : CollatzResearch.WordTrace tailWord_7029816 prefixEnd_7029816 3609674520667173046270471 := by
  unfold tailWord_7029816
  simp only [CollatzResearch.WordTrace]
  refine ⟨128199226750092351916750651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170932302333456469222334201 128199226750092351916750651)
  ·
    refine ⟨192298840125138527875125977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128199226750092351916750651 192298840125138527875125977)
    ·
      refine ⟨144224130093853895906344483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192298840125138527875125977 144224130093853895906344483)
      ·
        refine ⟨216336195140780843859516725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144224130093853895906344483 216336195140780843859516725)
        ·
          refine ⟨20281518294448204111829693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 216336195140780843859516725 20281518294448204111829693)
          ·
            refine ⟨7605569360418076541936135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20281518294448204111829693 7605569360418076541936135)
            ·
              refine ⟨11408354040627114812904203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7605569360418076541936135 11408354040627114812904203)
              ·
                refine ⟨17112531060940672219356305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11408354040627114812904203 17112531060940672219356305)
                ·
                  refine ⟨12834398295705504164517229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17112531060940672219356305 12834398295705504164517229)
                  ·
                    refine ⟨4812899360889564061693961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12834398295705504164517229 4812899360889564061693961)
                    ·
                      refine ⟨3609674520667173046270471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4812899360889564061693961 3609674520667173046270471)
                      ·
                        rfl

theorem cell23_7029816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 2, 3, 2].length) (baseStart_7029816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029816 prefixEnd_7029816 := by exact prefixLift 7029816
  have htrace : WordTrace (prefixWord ++ tailWord_7029816) baseStart_7029816 baseEnd_7029816 := by
    simpa [prefixWord, tailWord_7029816, baseEnd_7029816] using wordTrace_append hprefix tailTrace_7029816
  have hstable : (prefixWord ++ tailWord_7029816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029816).length < 2 ^ (prefixWord ++ tailWord_7029816).sum := by decide
  have hdescent : baseEnd_7029816 < baseStart_7029816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029829 : List Nat := [1, 3, 1, 1, 1, 3, 6, 1, 1, 1, 4]
def baseStart_7029829 : Nat := 118140960795 + 7029829 * 2 ^ 59
def prefixEnd_7029829 : Nat := 4983230072969 + 3 ^ 40 * 7029829 * 2
def baseEnd_7029829 : Nat := 3609681195915681495407911

theorem tailTrace_7029829 : CollatzResearch.WordTrace tailWord_7029829 prefixEnd_7029829 3609681195915681495407911 := by
  unfold tailWord_7029829
  simp only [CollatzResearch.WordTrace]
  refine ⟨256398927649137607053724541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170932618432758404702483027 256398927649137607053724541)
  ·
    refine ⟨96149597868426602645146703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256398927649137607053724541 96149597868426602645146703)
    ·
      refine ⟨144224396802639903967720055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96149597868426602645146703 144224396802639903967720055)
      ·
        refine ⟨216336595203959855951580083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144224396802639903967720055 216336595203959855951580083)
        ·
          refine ⟨324504892805939783927370125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216336595203959855951580083 324504892805939783927370125)
          ·
            refine ⟨121689334802227418972763797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324504892805939783927370125 121689334802227418972763797)
            ·
              refine ⟨5704187568854410264348303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121689334802227418972763797 5704187568854410264348303)
              ·
                refine ⟨8556281353281615396522455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5704187568854410264348303 8556281353281615396522455)
                ·
                  refine ⟨12834422029922423094783683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8556281353281615396522455 12834422029922423094783683)
                  ·
                    refine ⟨19251633044883634642175525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12834422029922423094783683 19251633044883634642175525)
                    ·
                      refine ⟨3609681195915681495407911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19251633044883634642175525 3609681195915681495407911)
                      ·
                        rfl

theorem cell23_7029829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 1, 1, 4].length) (baseStart_7029829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029829 prefixEnd_7029829 := by exact prefixLift 7029829
  have htrace : WordTrace (prefixWord ++ tailWord_7029829) baseStart_7029829 baseEnd_7029829 := by
    simpa [prefixWord, tailWord_7029829, baseEnd_7029829] using wordTrace_append hprefix tailTrace_7029829
  have hstable : (prefixWord ++ tailWord_7029829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029829).length < 2 ^ (prefixWord ++ tailWord_7029829).sum := by decide
  have hdescent : baseEnd_7029829 < baseStart_7029829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029866 : List Nat := [3, 1, 3, 2, 2, 2, 2, 2, 1, 2, 3]
def baseStart_7029866 : Nat := 118140960795 + 7029866 * 2 ^ 59
def prefixEnd_7029866 : Nat := 4983230072969 + 3 ^ 40 * 7029866 * 2
def baseEnd_7029866 : Nat := 3609700194699897850645241

theorem tailTrace_7029866 : CollatzResearch.WordTrace tailWord_7029866 prefixEnd_7029866 3609700194699897850645241 := by
  unfold tailWord_7029866
  simp only [CollatzResearch.WordTrace]
  refine ⟨64100069287500890593205363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170933518100002374915214301 64100069287500890593205363)
  ·
    refine ⟨96150103931251335889808045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64100069287500890593205363 96150103931251335889808045)
    ·
      refine ⟨36056288974219250958678017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96150103931251335889808045 36056288974219250958678017)
      ·
        refine ⟨27042216730664438219008513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36056288974219250958678017 27042216730664438219008513)
        ·
          refine ⟨20281662547998328664256385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27042216730664438219008513 20281662547998328664256385)
          ·
            refine ⟨15211246910998746498192289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20281662547998328664256385 15211246910998746498192289)
            ·
              refine ⟨11408435183249059873644217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15211246910998746498192289 11408435183249059873644217)
              ·
                refine ⟨8556326387436794905233163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11408435183249059873644217 8556326387436794905233163)
                ·
                  refine ⟨12834489581155192357849745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8556326387436794905233163 12834489581155192357849745)
                  ·
                    refine ⟨9625867185866394268387309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12834489581155192357849745 9625867185866394268387309)
                    ·
                      refine ⟨3609700194699897850645241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9625867185866394268387309 3609700194699897850645241)
                      ·
                        rfl

theorem cell23_7029866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_7029866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029866 prefixEnd_7029866 := by exact prefixLift 7029866
  have htrace : WordTrace (prefixWord ++ tailWord_7029866) baseStart_7029866 baseEnd_7029866 := by
    simpa [prefixWord, tailWord_7029866, baseEnd_7029866] using wordTrace_append hprefix tailTrace_7029866
  have hstable : (prefixWord ++ tailWord_7029866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029866).length < 2 ^ (prefixWord ++ tailWord_7029866).sum := by decide
  have hdescent : baseEnd_7029866 < baseStart_7029866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029869 : List Nat := [1, 5, 1, 1, 2, 4, 2, 7]
def baseStart_7029869 : Nat := 118140960795 + 7029869 * 2 ^ 59
def prefixEnd_7029869 : Nat := 4983230072969 + 3 ^ 40 * 7029869 * 2
def baseEnd_7029869 : Nat := 133692656857105975515101

theorem tailTrace_7029869 : CollatzResearch.WordTrace tailWord_7029869 prefixEnd_7029869 133692656857105975515101 := by
  unfold tailWord_7029869
  simp only [CollatzResearch.WordTrace]
  refine ⟨256400386568992693885180661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170933591045995129256787107 256400386568992693885180661)
  ·
    refine ⟨24037536240843065051735687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 256400386568992693885180661 24037536240843065051735687)
    ·
      refine ⟨36056304361264597577603531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24037536240843065051735687 36056304361264597577603531)
      ·
        refine ⟨54084456541896896366405297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36056304361264597577603531 54084456541896896366405297)
        ·
          refine ⟨40563342406422672274803973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54084456541896896366405297 40563342406422672274803973)
          ·
            refine ⟨7605626701204251051525745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40563342406422672274803973 7605626701204251051525745)
            ·
              refine ⟨5704220025903188288644309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7605626701204251051525745 5704220025903188288644309)
              ·
                refine ⟨133692656857105975515101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5704220025903188288644309 133692656857105975515101)
                ·
                  rfl

theorem cell23_7029869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 7].length) (baseStart_7029869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029869 prefixEnd_7029869 := by exact prefixLift 7029869
  have htrace : WordTrace (prefixWord ++ tailWord_7029869) baseStart_7029869 baseEnd_7029869 := by
    simpa [prefixWord, tailWord_7029869, baseEnd_7029869] using wordTrace_append hprefix tailTrace_7029869
  have hstable : (prefixWord ++ tailWord_7029869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029869).length < 2 ^ (prefixWord ++ tailWord_7029869).sum := by decide
  have hdescent : baseEnd_7029869 < baseStart_7029869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7029989 : List Nat := [1, 3, 1, 4, 3, 1, 1, 1, 1, 7]
def baseStart_7029989 : Nat := 118140960795 + 7029989 * 2 ^ 59
def prefixEnd_7029989 : Nat := 4983230072969 + 3 ^ 40 * 7029989 * 2
def baseEnd_7029989 : Nat := 1203254450940133623135725

theorem tailTrace_7029989 : CollatzResearch.WordTrace tailWord_7029989 prefixEnd_7029989 1203254450940133623135725 := by
  unfold tailWord_7029989
  simp only [CollatzResearch.WordTrace]
  refine ⟨256404763328557954379549021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170936508885705302919699347 256404763328557954379549021)
  ·
    refine ⟨96151786248209232892330883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256404763328557954379549021 96151786248209232892330883)
    ·
      refine ⟨144227679372313849338496325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96151786248209232892330883 144227679372313849338496325)
      ·
        refine ⟨27042689882308846750968061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144227679372313849338496325 27042689882308846750968061)
        ·
          refine ⟨10141008705865817531613023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27042689882308846750968061 10141008705865817531613023)
          ·
            refine ⟨15211513058798726297419535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10141008705865817531613023 15211513058798726297419535)
            ·
              refine ⟨22817269588198089446129303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15211513058798726297419535 22817269588198089446129303)
              ·
                refine ⟨34225904382297134169193955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22817269588198089446129303 34225904382297134169193955)
                ·
                  refine ⟨51338856573445701253790933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34225904382297134169193955 51338856573445701253790933)
                  ·
                    refine ⟨1203254450940133623135725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51338856573445701253790933 1203254450940133623135725)
                    ·
                      rfl

theorem cell23_7029989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 7].length) (baseStart_7029989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7029989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7029989 prefixEnd_7029989 := by exact prefixLift 7029989
  have htrace : WordTrace (prefixWord ++ tailWord_7029989) baseStart_7029989 baseEnd_7029989 := by
    simpa [prefixWord, tailWord_7029989, baseEnd_7029989] using wordTrace_append hprefix tailTrace_7029989
  have hstable : (prefixWord ++ tailWord_7029989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7029989).length < 2 ^ (prefixWord ++ tailWord_7029989).sum := by decide
  have hdescent : baseEnd_7029989 < baseStart_7029989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7029989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030009 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 4, 4, 2]
def baseStart_7030009 : Nat := 118140960795 + 7030009 * 2 ^ 59
def prefixEnd_7030009 : Nat := 4983230072969 + 3 ^ 40 * 7030009 * 2
def baseEnd_7030009 : Nat := 3609773622433490791157083

theorem tailTrace_7030009 : CollatzResearch.WordTrace tailWord_7030009 prefixEnd_7030009 3609773622433490791157083 := by
  unfold tailWord_7030009
  simp only [CollatzResearch.WordTrace]
  refine ⟨256405492788485497795277081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170936995192323665196851387 256405492788485497795277081)
  ·
    refine ⟨192304119591364123346457811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256405492788485497795277081 192304119591364123346457811)
    ·
      refine ⟨288456179387046185019686717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192304119591364123346457811 288456179387046185019686717)
      ·
        refine ⟨108171067270142319382382519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288456179387046185019686717 108171067270142319382382519)
        ·
          refine ⟨162256600905213479073573779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108171067270142319382382519 162256600905213479073573779)
          ·
            refine ⟨243384901357820218610360669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162256600905213479073573779 243384901357820218610360669)
            ·
              refine ⟨91269338009182581978885251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243384901357820218610360669 91269338009182581978885251)
              ·
                refine ⟨136904007013773872968327877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91269338009182581978885251 136904007013773872968327877)
                ·
                  refine ⟨25669501315082601181561477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136904007013773872968327877 25669501315082601181561477)
                  ·
                    refine ⟨4813031496577987721542777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25669501315082601181561477 4813031496577987721542777)
                    ·
                      refine ⟨3609773622433490791157083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4813031496577987721542777 3609773622433490791157083)
                      ·
                        rfl

theorem cell23_7030009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 4, 2].length) (baseStart_7030009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030009 prefixEnd_7030009 := by exact prefixLift 7030009
  have htrace : WordTrace (prefixWord ++ tailWord_7030009) baseStart_7030009 baseEnd_7030009 := by
    simpa [prefixWord, tailWord_7030009, baseEnd_7030009] using wordTrace_append hprefix tailTrace_7030009
  have hstable : (prefixWord ++ tailWord_7030009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030009).length < 2 ^ (prefixWord ++ tailWord_7030009).sum := by decide
  have hdescent : baseEnd_7030009 < baseStart_7030009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030019 : List Nat := [1, 1, 1, 3, 2, 4, 1, 3, 3, 4]
def baseStart_7030019 : Nat := 118140960795 + 7030019 * 2 ^ 59
def prefixEnd_7030019 : Nat := 4983230072969 + 3 ^ 40 * 7030019 * 2
def baseEnd_7030019 : Nat := 1203259585746678584010679

theorem tailTrace_7030019 : CollatzResearch.WordTrace tailWord_7030019 prefixEnd_7030019 1203259585746678584010679 := by
  unfold tailWord_7030019
  simp only [CollatzResearch.WordTrace]
  refine ⟨256405857518449269503141111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170937238345632846335427407 256405857518449269503141111)
  ·
    refine ⟨384608786277673904254711667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256405857518449269503141111 384608786277673904254711667)
    ·
      refine ⟨576913179416510856382067501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384608786277673904254711667 576913179416510856382067501)
      ·
        refine ⟨216342442281191571143275313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 576913179416510856382067501 216342442281191571143275313)
        ·
          refine ⟨162256831710893678357456485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216342442281191571143275313 162256831710893678357456485)
          ·
            refine ⟨30423155945792564692023091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162256831710893678357456485 30423155945792564692023091)
            ·
              refine ⟨45634733918688847038034637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30423155945792564692023091 45634733918688847038034637)
              ·
                refine ⟨17113025219508317639262989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45634733918688847038034637 17113025219508317639262989)
                ·
                  refine ⟨6417384457315619114723621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17113025219508317639262989 6417384457315619114723621)
                  ·
                    refine ⟨1203259585746678584010679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6417384457315619114723621 1203259585746678584010679)
                    ·
                      rfl

theorem cell23_7030019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 4].length) (baseStart_7030019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030019 prefixEnd_7030019 := by exact prefixLift 7030019
  have htrace : WordTrace (prefixWord ++ tailWord_7030019) baseStart_7030019 baseEnd_7030019 := by
    simpa [prefixWord, tailWord_7030019, baseEnd_7030019] using wordTrace_append hprefix tailTrace_7030019
  have hstable : (prefixWord ++ tailWord_7030019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030019).length < 2 ^ (prefixWord ++ tailWord_7030019).sum := by decide
  have hdescent : baseEnd_7030019 < baseStart_7030019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030053 : List Nat := [1, 3, 1, 2, 4, 1, 3, 3, 1, 4]
def baseStart_7030053 : Nat := 118140960795 + 7030053 * 2 ^ 59
def prefixEnd_7030053 : Nat := 4983230072969 + 3 ^ 40 * 7030053 * 2
def baseEnd_7030053 : Nat := 1203265405194096206335627

theorem tailTrace_7030053 : CollatzResearch.WordTrace tailWord_7030053 prefixEnd_7030053 1203265405194096206335627 := by
  unfold tailWord_7030053
  simp only [CollatzResearch.WordTrace]
  refine ⟨256407097600326093309878813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170938065066884062206585875 256407097600326093309878813)
  ·
    refine ⟨96152661600122284991204555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256407097600326093309878813 96152661600122284991204555)
    ·
      refine ⟨144228992400183427486806833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96152661600122284991204555 144228992400183427486806833)
      ·
        refine ⟨108171744300137570615105125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144228992400183427486806833 108171744300137570615105125)
        ·
          refine ⟨20282202056275794490332211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108171744300137570615105125 20282202056275794490332211)
          ·
            refine ⟨30423303084413691735498317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20282202056275794490332211 30423303084413691735498317)
            ·
              refine ⟨11408738656655134400811869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30423303084413691735498317 11408738656655134400811869)
              ·
                refine ⟨4278276996245675400304451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11408738656655134400811869 4278276996245675400304451)
                ·
                  refine ⟨6417415494368513100456677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4278276996245675400304451 6417415494368513100456677)
                  ·
                    refine ⟨1203265405194096206335627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6417415494368513100456677 1203265405194096206335627)
                    ·
                      rfl

theorem cell23_7030053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 1, 4].length) (baseStart_7030053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030053 prefixEnd_7030053 := by exact prefixLift 7030053
  have htrace : WordTrace (prefixWord ++ tailWord_7030053) baseStart_7030053 baseEnd_7030053 := by
    simpa [prefixWord, tailWord_7030053, baseEnd_7030053] using wordTrace_append hprefix tailTrace_7030053
  have hstable : (prefixWord ++ tailWord_7030053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030053).length < 2 ^ (prefixWord ++ tailWord_7030053).sum := by decide
  have hdescent : baseEnd_7030053 < baseStart_7030053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030072 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 2, 1, 7]
def baseStart_7030072 : Nat := 118140960795 + 7030072 * 2 ^ 59
def prefixEnd_7030072 : Nat := 4983230072969 + 3 ^ 40 * 7030072 * 2
def baseEnd_7030072 : Nat := 3609805971714724044669293

theorem tailTrace_7030072 : CollatzResearch.WordTrace tailWord_7030072 prefixEnd_7030072 3609805971714724044669293 := by
  unfold tailWord_7030072
  simp only [CollatzResearch.WordTrace]
  refine ⟨128203895293628629777410235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170938527058171506369880313 128203895293628629777410235)
  ·
    refine ⟨192305842940442944666115353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128203895293628629777410235 192305842940442944666115353)
    ·
      refine ⟨144229382205332208499586515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192305842940442944666115353 144229382205332208499586515)
      ·
        refine ⟨216344073307998312749379773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144229382205332208499586515 216344073307998312749379773)
        ·
          refine ⟨81129027490499367281017415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216344073307998312749379773 81129027490499367281017415)
          ·
            refine ⟨121693541235749050921526123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81129027490499367281017415 121693541235749050921526123)
            ·
              refine ⟨182540311853623576382289185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121693541235749050921526123 182540311853623576382289185)
              ·
                refine ⟨136905233890217682286716889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182540311853623576382289185 136905233890217682286716889)
                ·
                  refine ⟨102678925417663261715037667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136905233890217682286716889 102678925417663261715037667)
                  ·
                    refine ⟨154018388126494892572556501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102678925417663261715037667 154018388126494892572556501)
                    ·
                      refine ⟨3609805971714724044669293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154018388126494892572556501 3609805971714724044669293)
                      ·
                        rfl

theorem cell23_7030072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_7030072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030072 prefixEnd_7030072 := by exact prefixLift 7030072
  have htrace : WordTrace (prefixWord ++ tailWord_7030072) baseStart_7030072 baseEnd_7030072 := by
    simpa [prefixWord, tailWord_7030072, baseEnd_7030072] using wordTrace_append hprefix tailTrace_7030072
  have hstable : (prefixWord ++ tailWord_7030072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030072).length < 2 ^ (prefixWord ++ tailWord_7030072).sum := by decide
  have hdescent : baseEnd_7030072 < baseStart_7030072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030099 : List Nat := [1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 4]
def baseStart_7030099 : Nat := 118140960795 + 7030099 * 2 ^ 59
def prefixEnd_7030099 : Nat := 4983230072969 + 3 ^ 40 * 7030099 * 2
def baseEnd_7030099 : Nat := 3609819835692395439031669

theorem tailTrace_7030099 : CollatzResearch.WordTrace tailWord_7030099 prefixEnd_7030099 3609819835692395439031669 := by
  unfold tailWord_7030099
  simp only [CollatzResearch.WordTrace]
  refine ⟨256408775358159443166053351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170939183572106295444035567 256408775358159443166053351)
  ·
    refine ⟨384613163037239164749080027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256408775358159443166053351 384613163037239164749080027)
    ·
      refine ⟨576919744555858747123620041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384613163037239164749080027 576919744555858747123620041)
      ·
        refine ⟨432689808416894060342715031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 576919744555858747123620041 432689808416894060342715031)
        ·
          refine ⟨649034712625341090514072547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432689808416894060342715031 649034712625341090514072547)
          ·
            refine ⟨973552068938011635771108821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649034712625341090514072547 973552068938011635771108821)
            ·
              refine ⟨22817626615734647713385363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 973552068938011635771108821 22817626615734647713385363)
              ·
                refine ⟨34226439923601971570078045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22817626615734647713385363 34226439923601971570078045)
                ·
                  refine ⟨12834914971350739338779267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34226439923601971570078045 12834914971350739338779267)
                  ·
                    refine ⟨19252372457026109008168901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12834914971350739338779267 19252372457026109008168901)
                    ·
                      refine ⟨3609819835692395439031669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19252372457026109008168901 3609819835692395439031669)
                      ·
                        rfl

theorem cell23_7030099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 4].length) (baseStart_7030099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030099 prefixEnd_7030099 := by exact prefixLift 7030099
  have htrace : WordTrace (prefixWord ++ tailWord_7030099) baseStart_7030099 baseEnd_7030099 := by
    simpa [prefixWord, tailWord_7030099, baseEnd_7030099] using wordTrace_append hprefix tailTrace_7030099
  have hstable : (prefixWord ++ tailWord_7030099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030099).length < 2 ^ (prefixWord ++ tailWord_7030099).sum := by decide
  have hdescent : baseEnd_7030099 < baseStart_7030099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030103 : List Nat := [1, 1, 3, 2, 3, 3, 2, 1, 2, 3, 2]
def baseStart_7030103 : Nat := 118140960795 + 7030103 * 2 ^ 59
def prefixEnd_7030103 : Nat := 4983230072969 + 3 ^ 40 * 7030103 * 2
def baseEnd_7030103 : Nat := 3609821889615013423381651

theorem tailTrace_7030103 : CollatzResearch.WordTrace tailWord_7030103 prefixEnd_7030103 3609821889615013423381651 := by
  unfold tailWord_7030103
  simp only [CollatzResearch.WordTrace]
  refine ⟨256408921250144951849198963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170939280833429967899465975 256408921250144951849198963)
  ·
    refine ⟨384613381875217427773798445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256408921250144951849198963 384613381875217427773798445)
    ·
      refine ⟨144230018203206535415174417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384613381875217427773798445 144230018203206535415174417)
      ·
        refine ⟨108172513652404901561380813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144230018203206535415174417 108172513652404901561380813)
        ·
          refine ⟨40564692619651838085517805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108172513652404901561380813 40564692619651838085517805)
          ·
            refine ⟨15211759732369439282069177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40564692619651838085517805 15211759732369439282069177)
            ·
              refine ⟨11408819799277079461551883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15211759732369439282069177 11408819799277079461551883)
              ·
                refine ⟨17113229698915619192327825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11408819799277079461551883 17113229698915619192327825)
                ·
                  refine ⟨12834922274186714394245869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17113229698915619192327825 12834922274186714394245869)
                  ·
                    refine ⟨4813095852820017897842201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12834922274186714394245869 4813095852820017897842201)
                    ·
                      refine ⟨3609821889615013423381651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4813095852820017897842201 3609821889615013423381651)
                      ·
                        rfl

theorem cell23_7030103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 3, 2].length) (baseStart_7030103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030103 prefixEnd_7030103 := by exact prefixLift 7030103
  have htrace : WordTrace (prefixWord ++ tailWord_7030103) baseStart_7030103 baseEnd_7030103 := by
    simpa [prefixWord, tailWord_7030103, baseEnd_7030103] using wordTrace_append hprefix tailTrace_7030103
  have hstable : (prefixWord ++ tailWord_7030103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030103).length < 2 ^ (prefixWord ++ tailWord_7030103).sum := by decide
  have hdescent : baseEnd_7030103 < baseStart_7030103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030183 : List Nat := [1, 1, 6, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_7030183 : Nat := 118140960795 + 7030183 * 2 ^ 59
def prefixEnd_7030183 : Nat := 4983230072969 + 3 ^ 40 * 7030183 * 2
def baseEnd_7030183 : Nat := 3609862968067373110381283

theorem tailTrace_7030183 : CollatzResearch.WordTrace tailWord_7030183 prefixEnd_7030183 3609862968067373110381283 := by
  unfold tailWord_7030183
  simp only [CollatzResearch.WordTrace]
  refine ⟨256411839089855125512111203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170941226059903417008074135 256411839089855125512111203)
  ·
    refine ⟨384617758634782688268166805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256411839089855125512111203 384617758634782688268166805)
    ·
      refine ⟨18028957436005438512570319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 384617758634782688268166805 18028957436005438512570319)
      ·
        refine ⟨27043436154008157768855479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18028957436005438512570319 27043436154008157768855479)
        ·
          refine ⟨40565154231012236653283219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27043436154008157768855479 40565154231012236653283219)
          ·
            refine ⟨60847731346518354979924829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40565154231012236653283219 60847731346518354979924829)
            ·
              refine ⟨22817899254944383117471811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60847731346518354979924829 22817899254944383117471811)
              ·
                refine ⟨34226848882416574676207717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22817899254944383117471811 34226848882416574676207717)
                ·
                  refine ⟨6417534165453107751788947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34226848882416574676207717 6417534165453107751788947)
                  ·
                    refine ⟨9626301248179661627683421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6417534165453107751788947 9626301248179661627683421)
                    ·
                      refine ⟨3609862968067373110381283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9626301248179661627683421 3609862968067373110381283)
                      ·
                        rfl

theorem cell23_7030183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_7030183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030183 prefixEnd_7030183 := by exact prefixLift 7030183
  have htrace : WordTrace (prefixWord ++ tailWord_7030183) baseStart_7030183 baseEnd_7030183 := by
    simpa [prefixWord, tailWord_7030183, baseEnd_7030183] using wordTrace_append hprefix tailTrace_7030183
  have hstable : (prefixWord ++ tailWord_7030183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030183).length < 2 ^ (prefixWord ++ tailWord_7030183).sum := by decide
  have hdescent : baseEnd_7030183 < baseStart_7030183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030199 : List Nat := [1, 1, 3, 1, 3, 2, 1, 3, 2, 6]
def baseStart_7030199 : Nat := 118140960795 + 7030199 * 2 ^ 59
def prefixEnd_7030199 : Nat := 4983230072969 + 3 ^ 40 * 7030199 * 2
def baseEnd_7030199 : Nat := 1203290394585948349260403

theorem tailTrace_7030199 : CollatzResearch.WordTrace tailWord_7030199 prefixEnd_7030199 1203290394585948349260403 := by
  unfold tailWord_7030199
  simp only [CollatzResearch.WordTrace]
  refine ⟨256412422657797160244693651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170941615105198106829795767 256412422657797160244693651)
  ·
    refine ⟨384618633986695740367040477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256412422657797160244693651 384618633986695740367040477)
    ·
      refine ⟨144231987745010902637640179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384618633986695740367040477 144231987745010902637640179)
      ·
        refine ⟨216347981617516353956460269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144231987745010902637640179 216347981617516353956460269)
        ·
          refine ⟨81130493106568632733672601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216347981617516353956460269 81130493106568632733672601)
          ·
            refine ⟨60847869829926474550254451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81130493106568632733672601 60847869829926474550254451)
            ·
              refine ⟨91271804744889711825381677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60847869829926474550254451 91271804744889711825381677)
              ·
                refine ⟨34226926779333641934518129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91271804744889711825381677 34226926779333641934518129)
                ·
                  refine ⟨25670195084500231450888597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34226926779333641934518129 25670195084500231450888597)
                  ·
                    refine ⟨1203290394585948349260403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25670195084500231450888597 1203290394585948349260403)
                    ·
                      rfl

theorem cell23_7030199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_7030199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030199 prefixEnd_7030199 := by exact prefixLift 7030199
  have htrace : WordTrace (prefixWord ++ tailWord_7030199) baseStart_7030199 baseEnd_7030199 := by
    simpa [prefixWord, tailWord_7030199, baseEnd_7030199] using wordTrace_append hprefix tailTrace_7030199
  have hstable : (prefixWord ++ tailWord_7030199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030199).length < 2 ^ (prefixWord ++ tailWord_7030199).sum := by decide
  have hdescent : baseEnd_7030199 < baseStart_7030199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030219 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 4]
def baseStart_7030219 : Nat := 118140960795 + 7030219 * 2 ^ 59
def prefixEnd_7030219 : Nat := 4983230072969 + 3 ^ 40 * 7030219 * 2
def baseEnd_7030219 : Nat := 3609881453370934969531117

theorem tailTrace_7030219 : CollatzResearch.WordTrace tailWord_7030219 prefixEnd_7030219 3609881453370934969531117 := by
  unfold tailWord_7030219
  simp only [CollatzResearch.WordTrace]
  refine ⟨256413152117724703660421711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170942101411816469106947807 256413152117724703660421711)
  ·
    refine ⟨384619728176587055490632567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256413152117724703660421711 384619728176587055490632567)
    ·
      refine ⟨576929592264880583235948851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384619728176587055490632567 576929592264880583235948851)
      ·
        refine ⟨865394388397320874853923277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576929592264880583235948851 865394388397320874853923277)
        ·
          refine ⟨324522895648995328070221229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 865394388397320874853923277 324522895648995328070221229)
          ·
            refine ⟨121696085868373248026332961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324522895648995328070221229 121696085868373248026332961)
            ·
              refine ⟨91272064401279936019749721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121696085868373248026332961 91272064401279936019749721)
              ·
                refine ⟨68454048300959952014812291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91272064401279936019749721 68454048300959952014812291)
                ·
                  refine ⟨102681072451439928022218437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68454048300959952014812291 102681072451439928022218437)
                  ·
                    refine ⟨19252701084644986504165957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102681072451439928022218437 19252701084644986504165957)
                    ·
                      refine ⟨3609881453370934969531117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19252701084644986504165957 3609881453370934969531117)
                      ·
                        rfl

theorem cell23_7030219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 4].length) (baseStart_7030219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030219 prefixEnd_7030219 := by exact prefixLift 7030219
  have htrace : WordTrace (prefixWord ++ tailWord_7030219) baseStart_7030219 baseEnd_7030219 := by
    simpa [prefixWord, tailWord_7030219, baseEnd_7030219] using wordTrace_append hprefix tailTrace_7030219
  have hstable : (prefixWord ++ tailWord_7030219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030219).length < 2 ^ (prefixWord ++ tailWord_7030219).sum := by decide
  have hdescent : baseEnd_7030219 < baseStart_7030219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030223 : List Nat := [1, 1, 2, 1, 1, 4, 3, 2, 4, 2, 2]
def baseStart_7030223 : Nat := 118140960795 + 7030223 * 2 ^ 59
def prefixEnd_7030223 : Nat := 4983230072969 + 3 ^ 40 * 7030223 * 2
def baseEnd_7030223 : Nat := 3609883507293552953881099

theorem tailTrace_7030223 : CollatzResearch.WordTrace tailWord_7030223 prefixEnd_7030223 3609883507293552953881099 := by
  unfold tailWord_7030223
  simp only [CollatzResearch.WordTrace]
  refine ⟨256413298009710212343567323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170942198673140141562378215 256413298009710212343567323)
  ·
    refine ⟨384619947014565318515350985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256413298009710212343567323 384619947014565318515350985)
    ·
      refine ⟨288464960260923988886513239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384619947014565318515350985 288464960260923988886513239)
      ·
        refine ⟨432697440391385983329769859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288464960260923988886513239 432697440391385983329769859)
        ·
          refine ⟨649046160587078974994654789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432697440391385983329769859 649046160587078974994654789)
          ·
            refine ⟨121696155110077307811497773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 649046160587078974994654789 121696155110077307811497773)
            ·
              refine ⟨45636058166278990429311665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121696155110077307811497773 45636058166278990429311665)
              ·
                refine ⟨34227043624709242821983749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45636058166278990429311665 34227043624709242821983749)
                ·
                  refine ⟨6417570679632983029121953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34227043624709242821983749 6417570679632983029121953)
                  ·
                    refine ⟨4813178009724737271841465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6417570679632983029121953 4813178009724737271841465)
                    ·
                      refine ⟨3609883507293552953881099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4813178009724737271841465 3609883507293552953881099)
                      ·
                        rfl

theorem cell23_7030223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 2, 2].length) (baseStart_7030223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030223 prefixEnd_7030223 := by exact prefixLift 7030223
  have htrace : WordTrace (prefixWord ++ tailWord_7030223) baseStart_7030223 baseEnd_7030223 := by
    simpa [prefixWord, tailWord_7030223, baseEnd_7030223] using wordTrace_append hprefix tailTrace_7030223
  have hstable : (prefixWord ++ tailWord_7030223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030223).length < 2 ^ (prefixWord ++ tailWord_7030223).sum := by decide
  have hdescent : baseEnd_7030223 < baseStart_7030223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030239 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 7]
def baseStart_7030239 : Nat := 118140960795 + 7030239 * 2 ^ 59
def prefixEnd_7030239 : Nat := 4983230072969 + 3 ^ 40 * 7030239 * 2
def baseEnd_7030239 : Nat := 3609891722984024891281025

theorem tailTrace_7030239 : CollatzResearch.WordTrace tailWord_7030239 prefixEnd_7030239 3609891722984024891281025 := by
  unfold tailWord_7030239
  simp only [CollatzResearch.WordTrace]
  refine ⟨256413881577652247076149771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170942587718434831384099847 256413881577652247076149771)
  ·
    refine ⟨384620822366478370614224657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256413881577652247076149771 384620822366478370614224657)
    ·
      refine ⟨288465616774858777960668493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384620822366478370614224657 288465616774858777960668493)
      ·
        refine ⟨108174606290572041735250685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288465616774858777960668493 108174606290572041735250685)
        ·
          refine ⟨40565477358964515650719007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108174606290572041735250685 40565477358964515650719007)
          ·
            refine ⟨60848216038446773476078511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40565477358964515650719007 60848216038446773476078511)
            ·
              refine ⟨91272324057670160214117767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60848216038446773476078511 91272324057670160214117767)
              ·
                refine ⟨136908486086505240321176651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91272324057670160214117767 136908486086505240321176651)
                ·
                  refine ⟨205362729129757860481764977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136908486086505240321176651 205362729129757860481764977)
                  ·
                    refine ⟨154022046847318395361323733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 205362729129757860481764977 154022046847318395361323733)
                    ·
                      refine ⟨3609891722984024891281025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154022046847318395361323733 3609891722984024891281025)
                      ·
                        rfl

theorem cell23_7030239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_7030239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030239 prefixEnd_7030239 := by exact prefixLift 7030239
  have htrace : WordTrace (prefixWord ++ tailWord_7030239) baseStart_7030239 baseEnd_7030239 := by
    simpa [prefixWord, tailWord_7030239, baseEnd_7030239] using wordTrace_append hprefix tailTrace_7030239
  have hstable : (prefixWord ++ tailWord_7030239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030239).length < 2 ^ (prefixWord ++ tailWord_7030239).sum := by decide
  have hdescent : baseEnd_7030239 < baseStart_7030239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030257 : List Nat := [1, 2, 2, 2, 3, 2, 4, 1, 2, 2, 2]
def baseStart_7030257 : Nat := 118140960795 + 7030257 * 2 ^ 59
def prefixEnd_7030257 : Nat := 4983230072969 + 3 ^ 40 * 7030257 * 2
def baseEnd_7030257 : Nat := 3609900965635805820855943

theorem tailTrace_7030257 : CollatzResearch.WordTrace tailWord_7030257 prefixEnd_7030257 3609900965635805820855943 := by
  unfold tailWord_7030257
  simp only [CollatzResearch.WordTrace]
  refine ⟨256414538091587036150305025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170943025394391357433536683 256414538091587036150305025)
  ·
    refine ⟨192310903568690277112728769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256414538091587036150305025 192310903568690277112728769)
    ·
      refine ⟨144233177676517707834546577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192310903568690277112728769 144233177676517707834546577)
      ·
        refine ⟨108174883257388280875909933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144233177676517707834546577 108174883257388280875909933)
        ·
          refine ⟨40565581221520605328466225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108174883257388280875909933 40565581221520605328466225)
          ·
            refine ⟨30424185916140453996349669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40565581221520605328466225 30424185916140453996349669)
            ·
              refine ⟨5704534859276335124315563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30424185916140453996349669 5704534859276335124315563)
              ·
                refine ⟨8556802288914502686473345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5704534859276335124315563 8556802288914502686473345)
                ·
                  refine ⟨6417601716685877014855009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8556802288914502686473345 6417601716685877014855009)
                  ·
                    refine ⟨4813201287514407761141257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6417601716685877014855009 4813201287514407761141257)
                    ·
                      refine ⟨3609900965635805820855943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4813201287514407761141257 3609900965635805820855943)
                      ·
                        rfl

theorem cell23_7030257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 2, 2, 2].length) (baseStart_7030257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030257 prefixEnd_7030257 := by exact prefixLift 7030257
  have htrace : WordTrace (prefixWord ++ tailWord_7030257) baseStart_7030257 baseEnd_7030257 := by
    simpa [prefixWord, tailWord_7030257, baseEnd_7030257] using wordTrace_append hprefix tailTrace_7030257
  have hstable : (prefixWord ++ tailWord_7030257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030257).length < 2 ^ (prefixWord ++ tailWord_7030257).sum := by decide
  have hdescent : baseEnd_7030257 < baseStart_7030257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030259 : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 1, 7]
def baseStart_7030259 : Nat := 118140960795 + 7030259 * 2 ^ 59
def prefixEnd_7030259 : Nat := 4983230072969 + 3 ^ 40 * 7030259 * 2
def baseEnd_7030259 : Nat := 1203300664199038271010311

theorem tailTrace_7030259 : CollatzResearch.WordTrace tailWord_7030259 prefixEnd_7030259 1203300664199038271010311 := by
  unfold tailWord_7030259
  simp only [CollatzResearch.WordTrace]
  refine ⟨256414611037579790491877831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170943074025053193661251887 256414611037579790491877831)
  ·
    refine ⟨384621916556369685737816747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256414611037579790491877831 384621916556369685737816747)
    ·
      refine ⟨576932874834554528606725121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384621916556369685737816747 576932874834554528606725121)
      ·
        refine ⟨432699656125915896455043841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 576932874834554528606725121 432699656125915896455043841)
        ·
          refine ⟨324524742094436922341282881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 432699656125915896455043841 324524742094436922341282881)
          ·
            refine ⟨243393556570827691755962161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324524742094436922341282881 243393556570827691755962161)
            ·
              refine ⟨182545167428120768816971621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243393556570827691755962161 182545167428120768816971621)
              ·
                refine ⟨34227218892772644153182179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182545167428120768816971621 34227218892772644153182179)
                ·
                  refine ⟨51340828339158966229773269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34227218892772644153182179 51340828339158966229773269)
                  ·
                    refine ⟨1203300664199038271010311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51340828339158966229773269 1203300664199038271010311)
                    ·
                      rfl

theorem cell23_7030259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 7].length) (baseStart_7030259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030259 prefixEnd_7030259 := by exact prefixLift 7030259
  have htrace : WordTrace (prefixWord ++ tailWord_7030259) baseStart_7030259 baseEnd_7030259 := by
    simpa [prefixWord, tailWord_7030259, baseEnd_7030259] using wordTrace_append hprefix tailTrace_7030259
  have hstable : (prefixWord ++ tailWord_7030259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030259).length < 2 ^ (prefixWord ++ tailWord_7030259).sum := by decide
  have hdescent : baseEnd_7030259 < baseStart_7030259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030278 : List Nat := [6, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_7030278 : Nat := 118140960795 + 7030278 * 2 ^ 59
def prefixEnd_7030278 : Nat := 4983230072969 + 3 ^ 40 * 7030278 * 2
def baseEnd_7030278 : Nat := 3609911748729550238693347

theorem tailTrace_7030278 : CollatzResearch.WordTrace tailWord_7030278 prefixEnd_7030278 3609911748729550238693347 := by
  unfold tailWord_7030278
  simp only [CollatzResearch.WordTrace]
  refine ⟨8012978250765967398025609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 170943536016340637824546325 8012978250765967398025609)
  ·
    refine ⟨6009733688074475548519207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8012978250765967398025609 6009733688074475548519207)
    ·
      refine ⟨9014600532111713322778811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6009733688074475548519207 9014600532111713322778811)
      ·
        refine ⟨13521900798167569984168217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9014600532111713322778811 13521900798167569984168217)
        ·
          refine ⟨10141425598625677488126163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13521900798167569984168217 10141425598625677488126163)
          ·
            refine ⟨15212138397938516232189245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10141425598625677488126163 15212138397938516232189245)
            ·
              refine ⟨5704551899226943587070967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15212138397938516232189245 5704551899226943587070967)
              ·
                refine ⟨8556827848840415380606451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5704551899226943587070967 8556827848840415380606451)
                ·
                  refine ⟨12835241773260623070909677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8556827848840415380606451 12835241773260623070909677)
                  ·
                    refine ⟨4813215664972733651591129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12835241773260623070909677 4813215664972733651591129)
                    ·
                      refine ⟨3609911748729550238693347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4813215664972733651591129 3609911748729550238693347)
                      ·
                        rfl

theorem cell23_7030278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_7030278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030278 prefixEnd_7030278 := by exact prefixLift 7030278
  have htrace : WordTrace (prefixWord ++ tailWord_7030278) baseStart_7030278 baseEnd_7030278 := by
    simpa [prefixWord, tailWord_7030278, baseEnd_7030278] using wordTrace_append hprefix tailTrace_7030278
  have hstable : (prefixWord ++ tailWord_7030278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030278).length < 2 ^ (prefixWord ++ tailWord_7030278).sum := by decide
  have hdescent : baseEnd_7030278 < baseStart_7030278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030323 : List Nat := [1, 1, 1, 2, 4, 4, 1, 2, 3, 4]
def baseStart_7030323 : Nat := 118140960795 + 7030323 * 2 ^ 59
def prefixEnd_7030323 : Nat := 4983230072969 + 3 ^ 40 * 7030323 * 2
def baseEnd_7030323 : Nat := 1203311618453000854210213

theorem tailTrace_7030323 : CollatzResearch.WordTrace tailWord_7030323 prefixEnd_7030323 1203311618453000854210213 := by
  unfold tailWord_7030323
  simp only [CollatzResearch.WordTrace]
  refine ⟨256416945309347929422207623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170944630206231952948138415 256416945309347929422207623)
  ·
    refine ⟨384625417964021894133311435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256416945309347929422207623 384625417964021894133311435)
    ·
      refine ⟨576938126946032841199967153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384625417964021894133311435 576938126946032841199967153)
      ·
        refine ⟨432703595209524630899975365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 576938126946032841199967153 432703595209524630899975365)
        ·
          refine ⟨81131924101785868293745381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 432703595209524630899975365 81131924101785868293745381)
          ·
            refine ⟨15212235769084850305077259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81131924101785868293745381 15212235769084850305077259)
            ·
              refine ⟨22818353653627275457615889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15212235769084850305077259 22818353653627275457615889)
              ·
                refine ⟨17113765240220456593211917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22818353653627275457615889 17113765240220456593211917)
                ·
                  refine ⟨6417661965082671222454469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17113765240220456593211917 6417661965082671222454469)
                  ·
                    refine ⟨1203311618453000854210213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6417661965082671222454469 1203311618453000854210213)
                    ·
                      rfl

theorem cell23_7030323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 4].length) (baseStart_7030323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030323 prefixEnd_7030323 := by exact prefixLift 7030323
  have htrace : WordTrace (prefixWord ++ tailWord_7030323) baseStart_7030323 baseEnd_7030323 := by
    simpa [prefixWord, tailWord_7030323, baseEnd_7030323] using wordTrace_append hprefix tailTrace_7030323
  have hstable : (prefixWord ++ tailWord_7030323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030323).length < 2 ^ (prefixWord ++ tailWord_7030323).sum := by decide
  have hdescent : baseEnd_7030323 < baseStart_7030323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030356 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_7030356 : Nat := 118140960795 + 7030356 * 2 ^ 59
def prefixEnd_7030356 : Nat := 4983230072969 + 3 ^ 40 * 7030356 * 2
def baseEnd_7030356 : Nat := 3609951800220600933517987

theorem tailTrace_7030356 : CollatzResearch.WordTrace tailWord_7030356 prefixEnd_7030356 3609951800220600933517987 := by
  unfold tailWord_7030356
  simp only [CollatzResearch.WordTrace]
  refine ⟨128209074459114188029079461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170945432612152250705439281 128209074459114188029079461)
  ·
    refine ⟨24039201461083910255452399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128209074459114188029079461 24039201461083910255452399)
    ·
      refine ⟨36058802191625865383178599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24039201461083910255452399 36058802191625865383178599)
      ·
        refine ⟨54088203287438798074767899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36058802191625865383178599 54088203287438798074767899)
        ·
          refine ⟨81132304931158197112151849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54088203287438798074767899 81132304931158197112151849)
          ·
            refine ⟨60849228698368647834113887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81132304931158197112151849 60849228698368647834113887)
            ·
              refine ⟨91273843047552971751170831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60849228698368647834113887 91273843047552971751170831)
              ·
                refine ⟨136910764571329457626756247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91273843047552971751170831 136910764571329457626756247)
                ·
                  refine ⟨205366146856994186440134371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136910764571329457626756247 205366146856994186440134371)
                  ·
                    refine ⟨308049220285491279660201557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 205366146856994186440134371 308049220285491279660201557)
                    ·
                      refine ⟨3609951800220600933517987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 308049220285491279660201557 3609951800220600933517987)
                      ·
                        rfl

theorem cell23_7030356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_7030356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030356 prefixEnd_7030356 := by exact prefixLift 7030356
  have htrace : WordTrace (prefixWord ++ tailWord_7030356) baseStart_7030356 baseEnd_7030356 := by
    simpa [prefixWord, tailWord_7030356, baseEnd_7030356] using wordTrace_append hprefix tailTrace_7030356
  have hstable : (prefixWord ++ tailWord_7030356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030356).length < 2 ^ (prefixWord ++ tailWord_7030356).sum := by decide
  have hdescent : baseEnd_7030356 < baseStart_7030356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030396 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 3, 6]
def baseStart_7030396 : Nat := 118140960795 + 7030396 * 2 ^ 59
def prefixEnd_7030396 : Nat := 4983230072969 + 3 ^ 40 * 7030396 * 2
def baseEnd_7030396 : Nat := 1203324113148926925672601

theorem tailTrace_7030396 : CollatzResearch.WordTrace tailWord_7030396 prefixEnd_7030396 1203324113148926925672601 := by
  unfold tailWord_7030396
  simp only [CollatzResearch.WordTrace]
  refine ⟨128209803919041731444807521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170946405225388975259743361 128209803919041731444807521)
  ·
    refine ⟨96157352939281298583605641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128209803919041731444807521 96157352939281298583605641)
    ·
      refine ⟨72118014704460973937704231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96157352939281298583605641 72118014704460973937704231)
      ·
        refine ⟨108177022056691460906556347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72118014704460973937704231 108177022056691460906556347)
        ·
          refine ⟨162265533085037191359834521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108177022056691460906556347 162265533085037191359834521)
          ·
            refine ⟨121699149813777893519875891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162265533085037191359834521 121699149813777893519875891)
            ·
              refine ⟨182548724720666840279813837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121699149813777893519875891 182548724720666840279813837)
              ·
                refine ⟨68455771770250065104930189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182548724720666840279813837 68455771770250065104930189)
                ·
                  refine ⟨25670914413843774414348821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68455771770250065104930189 25670914413843774414348821)
                  ·
                    refine ⟨1203324113148926925672601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25670914413843774414348821 1203324113148926925672601)
                    ·
                      rfl

theorem cell23_7030396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_7030396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030396 prefixEnd_7030396 := by exact prefixLift 7030396
  have htrace : WordTrace (prefixWord ++ tailWord_7030396) baseStart_7030396 baseEnd_7030396 := by
    simpa [prefixWord, tailWord_7030396, baseEnd_7030396] using wordTrace_append hprefix tailTrace_7030396
  have hstable : (prefixWord ++ tailWord_7030396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030396).length < 2 ^ (prefixWord ++ tailWord_7030396).sum := by decide
  have hdescent : baseEnd_7030396 < baseStart_7030396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030423 : List Nat := [1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 5]
def baseStart_7030423 : Nat := 118140960795 + 7030423 * 2 ^ 59
def prefixEnd_7030423 : Nat := 4983230072969 + 3 ^ 40 * 7030423 * 2
def baseEnd_7030423 : Nat := 3609986203424452171380179

theorem tailTrace_7030423 : CollatzResearch.WordTrace tailWord_7030423 prefixEnd_7030423 3609986203424452171380179 := by
  unfold tailWord_7030423
  simp only [CollatzResearch.WordTrace]
  refine ⟨256420592608985646500847923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170947061739323764333898615 256420592608985646500847923)
  ·
    refine ⟨384630888913478469751271885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256420592608985646500847923 384630888913478469751271885)
    ·
      refine ⟨144236583342554426156726957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384630888913478469751271885 144236583342554426156726957)
      ·
        refine ⟨54088718753457909808772609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144236583342554426156726957 54088718753457909808772609)
        ·
          refine ⟨40566539065093432356579457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54088718753457909808772609 40566539065093432356579457)
          ·
            refine ⟨30424904298820074267434593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40566539065093432356579457 30424904298820074267434593)
            ·
              refine ⟨22818678224115055700575945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30424904298820074267434593 22818678224115055700575945)
              ·
                refine ⟨17114008668086291775431959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22818678224115055700575945 17114008668086291775431959)
                ·
                  refine ⟨25671013002129437663147939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17114008668086291775431959 25671013002129437663147939)
                  ·
                    refine ⟨38506519503194156494721909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25671013002129437663147939 38506519503194156494721909)
                    ·
                      refine ⟨3609986203424452171380179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38506519503194156494721909 3609986203424452171380179)
                      ·
                        rfl

theorem cell23_7030423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_7030423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030423 prefixEnd_7030423 := by exact prefixLift 7030423
  have htrace : WordTrace (prefixWord ++ tailWord_7030423) baseStart_7030423 baseEnd_7030423 := by
    simpa [prefixWord, tailWord_7030423, baseEnd_7030423] using wordTrace_append hprefix tailTrace_7030423
  have hstable : (prefixWord ++ tailWord_7030423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030423).length < 2 ^ (prefixWord ++ tailWord_7030423).sum := by decide
  have hdescent : baseEnd_7030423 < baseStart_7030423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030433 : List Nat := [1, 2, 3, 3, 2, 1, 2, 1, 1, 1, 6]
def baseStart_7030433 : Nat := 118140960795 + 7030433 * 2 ^ 59
def prefixEnd_7030433 : Nat := 4983230072969 + 3 ^ 40 * 7030433 * 2
def baseEnd_7030433 : Nat := 3609991338230997132255133

theorem tailTrace_7030433 : CollatzResearch.WordTrace tailWord_7030433 prefixEnd_7030433 3609991338230997132255133 := by
  unfold tailWord_7030433
  simp only [CollatzResearch.WordTrace]
  refine ⟨256420957338949418208711953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170947304892632945472474635 256420957338949418208711953)
  ·
    refine ⟨192315718004212063656533965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256420957338949418208711953 192315718004212063656533965)
    ·
      refine ⟨72118394251579523871200237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192315718004212063656533965 72118394251579523871200237)
      ·
        refine ⟨27044397844342321451700089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72118394251579523871200237 27044397844342321451700089)
        ·
          refine ⟨20283298383256741088775067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27044397844342321451700089 20283298383256741088775067)
          ·
            refine ⟨30424947574885111633162601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20283298383256741088775067 30424947574885111633162601)
            ·
              refine ⟨22818710681163833724871951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30424947574885111633162601 22818710681163833724871951)
              ·
                refine ⟨34228066021745750587307927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22818710681163833724871951 34228066021745750587307927)
                ·
                  refine ⟨51342099032618625880961891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34228066021745750587307927 51342099032618625880961891)
                  ·
                    refine ⟨77013148548927938821442837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51342099032618625880961891 77013148548927938821442837)
                    ·
                      refine ⟨3609991338230997132255133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77013148548927938821442837 3609991338230997132255133)
                      ·
                        rfl

theorem cell23_7030433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_7030433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030433 prefixEnd_7030433 := by exact prefixLift 7030433
  have htrace : WordTrace (prefixWord ++ tailWord_7030433) baseStart_7030433 baseEnd_7030433 := by
    simpa [prefixWord, tailWord_7030433, baseEnd_7030433] using wordTrace_append hprefix tailTrace_7030433
  have hstable : (prefixWord ++ tailWord_7030433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030433).length < 2 ^ (prefixWord ++ tailWord_7030433).sum := by decide
  have hdescent : baseEnd_7030433 < baseStart_7030433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030434 : List Nat := [3, 3, 1, 4, 1, 2, 1, 2, 1, 5]
def baseStart_7030434 : Nat := 118140960795 + 7030434 * 2 ^ 59
def prefixEnd_7030434 : Nat := 4983230072969 + 3 ^ 40 * 7030434 * 2
def baseEnd_7030434 : Nat := 1203330617237217209447543

theorem tailTrace_7030434 : CollatzResearch.WordTrace tailWord_7030434 prefixEnd_7030434 1203330617237217209447543 := by
  unfold tailWord_7030434
  simp only [CollatzResearch.WordTrace]
  refine ⟨64105248452986448844874589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170947329207963863586332237 64105248452986448844874589)
  ·
    refine ⟨24039468169869918316827971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64105248452986448844874589 24039468169869918316827971)
    ·
      refine ⟨36059202254804877475241957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24039468169869918316827971 36059202254804877475241957)
      ·
        refine ⟨6761100422775914526607867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36059202254804877475241957 6761100422775914526607867)
        ·
          refine ⟨10141650634163871789911801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6761100422775914526607867 10141650634163871789911801)
          ·
            refine ⟨7606237975622903842433851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10141650634163871789911801 7606237975622903842433851)
            ·
              refine ⟨11409356963434355763650777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7606237975622903842433851 11409356963434355763650777)
              ·
                refine ⟨8557017722575766822738083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11409356963434355763650777 8557017722575766822738083)
                ·
                  refine ⟨12835526583863650234107125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8557017722575766822738083 12835526583863650234107125)
                  ·
                    refine ⟨1203330617237217209447543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12835526583863650234107125 1203330617237217209447543)
                    ·
                      rfl

theorem cell23_7030434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_7030434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030434 prefixEnd_7030434 := by exact prefixLift 7030434
  have htrace : WordTrace (prefixWord ++ tailWord_7030434) baseStart_7030434 baseEnd_7030434 := by
    simpa [prefixWord, tailWord_7030434, baseEnd_7030434] using wordTrace_append hprefix tailTrace_7030434
  have hstable : (prefixWord ++ tailWord_7030434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030434).length < 2 ^ (prefixWord ++ tailWord_7030434).sum := by decide
  have hdescent : baseEnd_7030434 < baseStart_7030434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030456 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 4, 7]
def baseStart_7030456 : Nat := 118140960795 + 7030456 * 2 ^ 59
def prefixEnd_7030456 : Nat := 4983230072969 + 3 ^ 40 * 7030456 * 2
def baseEnd_7030456 : Nat := 1203334382762016847422509

theorem tailTrace_7030456 : CollatzResearch.WordTrace tailWord_7030456 prefixEnd_7030456 1203334382762016847422509 := by
  unfold tailWord_7030456
  simp only [CollatzResearch.WordTrace]
  refine ⟨128210898108933046568399611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170947864145244062091199481 128210898108933046568399611)
  ·
    refine ⟨192316347163399569852599417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128210898108933046568399611 192316347163399569852599417)
    ·
      refine ⟨144237260372549677389449563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192316347163399569852599417 144237260372549677389449563)
      ·
        refine ⟨216355890558824516084174345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144237260372549677389449563 216355890558824516084174345)
        ·
          refine ⟨162266917919118387063130759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216355890558824516084174345 162266917919118387063130759)
          ·
            refine ⟨243400376878677580594696139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162266917919118387063130759 243400376878677580594696139)
            ·
              refine ⟨365100565318016370892044209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243400376878677580594696139 365100565318016370892044209)
              ·
                refine ⟨273825423988512278169033157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 365100565318016370892044209 273825423988512278169033157)
                ·
                  refine ⟨51342266997846052156693717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 273825423988512278169033157 51342266997846052156693717)
                  ·
                    refine ⟨1203334382762016847422509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51342266997846052156693717 1203334382762016847422509)
                    ·
                      rfl

theorem cell23_7030456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_7030456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030456 prefixEnd_7030456 := by exact prefixLift 7030456
  have htrace : WordTrace (prefixWord ++ tailWord_7030456) baseStart_7030456 baseEnd_7030456 := by
    simpa [prefixWord, tailWord_7030456, baseEnd_7030456] using wordTrace_append hprefix tailTrace_7030456
  have hstable : (prefixWord ++ tailWord_7030456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030456).length < 2 ^ (prefixWord ++ tailWord_7030456).sum := by decide
  have hdescent : baseEnd_7030456 < baseStart_7030456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030477 : List Nat := [1, 6, 2, 1, 1, 3, 1, 8]
def baseStart_7030477 : Nat := 118140960795 + 7030477 * 2 ^ 59
def prefixEnd_7030477 : Nat := 4983230072969 + 3 ^ 40 * 7030477 * 2
def baseEnd_7030477 : Nat := 133704219680733146670553

theorem tailTrace_7030477 : CollatzResearch.WordTrace tailWord_7030477 prefixEnd_7030477 133704219680733146670553 := by
  unfold tailWord_7030477
  simp only [CollatzResearch.WordTrace]
  refine ⟨256422562150790013723313685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170948374767193342482209123 256422562150790013723313685)
  ·
    refine ⟨12019807600818281893280329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 256422562150790013723313685 12019807600818281893280329)
    ·
      refine ⟨9014855700613711419960247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12019807600818281893280329 9014855700613711419960247)
      ·
        refine ⟨13522283550920567129940371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9014855700613711419960247 13522283550920567129940371)
        ·
          refine ⟨20283425326380850694910557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13522283550920567129940371 20283425326380850694910557)
          ·
            refine ⟨7606284497392819010591459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20283425326380850694910557 7606284497392819010591459)
            ·
              refine ⟨11409426746089228515887189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7606284497392819010591459 11409426746089228515887189)
              ·
                refine ⟨133704219680733146670553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11409426746089228515887189 133704219680733146670553)
                ·
                  rfl

theorem cell23_7030477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 8].length) (baseStart_7030477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030477 prefixEnd_7030477 := by exact prefixLift 7030477
  have htrace : WordTrace (prefixWord ++ tailWord_7030477) baseStart_7030477 baseEnd_7030477 := by
    simpa [prefixWord, tailWord_7030477, baseEnd_7030477] using wordTrace_append hprefix tailTrace_7030477
  have hstable : (prefixWord ++ tailWord_7030477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030477).length < 2 ^ (prefixWord ++ tailWord_7030477).sum := by decide
  have hdescent : baseEnd_7030477 < baseStart_7030477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030543 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 3]
def baseStart_7030543 : Nat := 118140960795 + 7030543 * 2 ^ 59
def prefixEnd_7030543 : Nat := 4983230072969 + 3 ^ 40 * 7030543 * 2
def baseEnd_7030543 : Nat := 3610047821102991701879627

theorem tailTrace_7030543 : CollatzResearch.WordTrace tailWord_7030543 prefixEnd_7030543 3610047821102991701879627 := by
  unfold tailWord_7030543
  simp only [CollatzResearch.WordTrace]
  refine ⟨256424969368550906995216283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170949979579033937996810855 256424969368550906995216283)
  ·
    refine ⟨384637454052826360492824425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256424969368550906995216283 384637454052826360492824425)
    ·
      refine ⟨288478090539619770369618319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384637454052826360492824425 288478090539619770369618319)
      ·
        refine ⟨432717135809429655554427479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288478090539619770369618319 432717135809429655554427479)
        ·
          refine ⟨649075703714144483331641219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432717135809429655554427479 649075703714144483331641219)
          ·
            refine ⟨973613555571216724997461829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649075703714144483331641219 973613555571216724997461829)
            ·
              refine ⟨182552541669603135937024093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 973613555571216724997461829 182552541669603135937024093)
              ·
                refine ⟨68457203126101175976384035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182552541669603135937024093 68457203126101175976384035)
                ·
                  refine ⟨102685804689151763964576053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68457203126101175976384035 102685804689151763964576053)
                  ·
                    refine ⟨9626794189607977871679005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102685804689151763964576053 9626794189607977871679005)
                    ·
                      refine ⟨3610047821102991701879627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9626794189607977871679005 3610047821102991701879627)
                      ·
                        rfl

theorem cell23_7030543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 3].length) (baseStart_7030543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030543 prefixEnd_7030543 := by exact prefixLift 7030543
  have htrace : WordTrace (prefixWord ++ tailWord_7030543) baseStart_7030543 baseEnd_7030543 := by
    simpa [prefixWord, tailWord_7030543, baseEnd_7030543] using wordTrace_append hprefix tailTrace_7030543
  have hstable : (prefixWord ++ tailWord_7030543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030543).length < 2 ^ (prefixWord ++ tailWord_7030543).sum := by decide
  have hdescent : baseEnd_7030543 < baseStart_7030543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030563 : List Nat := [1, 1, 1, 4, 2, 1, 4, 1, 1, 7]
def baseStart_7030563 : Nat := 118140960795 + 7030563 * 2 ^ 59
def prefixEnd_7030563 : Nat := 4983230072969 + 3 ^ 40 * 7030563 * 2
def baseEnd_7030563 : Nat := 1203352696905360541209845

theorem tailTrace_7030563 : CollatzResearch.WordTrace tailWord_7030563 prefixEnd_7030563 1203352696905360541209845 := by
  unfold tailWord_7030563
  simp only [CollatzResearch.WordTrace]
  refine ⟨256425698828478450410944343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170950465885652300273962895 256425698828478450410944343)
  ·
    refine ⟨384638548242717675616416515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256425698828478450410944343 384638548242717675616416515)
    ·
      refine ⟨576957822364076513424624773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384638548242717675616416515 576957822364076513424624773)
      ·
        refine ⟨108179591693264346267117145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 576957822364076513424624773 108179591693264346267117145)
        ·
          refine ⟨81134693769948259700337859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108179591693264346267117145 81134693769948259700337859)
          ·
            refine ⟨121702040654922389550506789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81134693769948259700337859 121702040654922389550506789)
            ·
              refine ⟨22819132622797948040720023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121702040654922389550506789 22819132622797948040720023)
              ·
                refine ⟨34228698934196922061080035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22819132622797948040720023 34228698934196922061080035)
                ·
                  refine ⟨51343048401295383091620053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34228698934196922061080035 51343048401295383091620053)
                  ·
                    refine ⟨1203352696905360541209845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51343048401295383091620053 1203352696905360541209845)
                    ·
                      rfl

theorem cell23_7030563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 7].length) (baseStart_7030563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030563 prefixEnd_7030563 := by exact prefixLift 7030563
  have htrace : WordTrace (prefixWord ++ tailWord_7030563) baseStart_7030563 baseEnd_7030563 := by
    simpa [prefixWord, tailWord_7030563, baseEnd_7030563] using wordTrace_append hprefix tailTrace_7030563
  have hstable : (prefixWord ++ tailWord_7030563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030563).length < 2 ^ (prefixWord ++ tailWord_7030563).sum := by decide
  have hdescent : baseEnd_7030563 < baseStart_7030563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030583 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 4]
def baseStart_7030583 : Nat := 118140960795 + 7030583 * 2 ^ 59
def prefixEnd_7030583 : Nat := 4983230072969 + 3 ^ 40 * 7030583 * 2
def baseEnd_7030583 : Nat := 3610068360329171545379443

theorem tailTrace_7030583 : CollatzResearch.WordTrace tailWord_7030583 prefixEnd_7030583 3610068360329171545379443 := by
  unfold tailWord_7030583
  simp only [CollatzResearch.WordTrace]
  refine ⟨256426428288405993826672403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170950952192270662551114935 256426428288405993826672403)
  ·
    refine ⟨384639642432608990740008605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256426428288405993826672403 384639642432608990740008605)
    ·
      refine ⟨144239865912228371527503227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384639642432608990740008605 144239865912228371527503227)
      ·
        refine ⟨216359798868342557291254841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144239865912228371527503227 216359798868342557291254841)
        ·
          refine ⟨162269849151256917968441131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216359798868342557291254841 162269849151256917968441131)
          ·
            refine ⟨243404773726885376952661697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162269849151256917968441131 243404773726885376952661697)
            ·
              refine ⟨182553580295164032714496273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243404773726885376952661697 182553580295164032714496273)
              ·
                refine ⟨136915185221373024535872205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182553580295164032714496273 136915185221373024535872205)
                ·
                  refine ⟨51343194458014884200952077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136915185221373024535872205 51343194458014884200952077)
                  ·
                    refine ⟨19253697921755581575357029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51343194458014884200952077 19253697921755581575357029)
                    ·
                      refine ⟨3610068360329171545379443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19253697921755581575357029 3610068360329171545379443)
                      ·
                        rfl

theorem cell23_7030583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_7030583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030583 prefixEnd_7030583 := by exact prefixLift 7030583
  have htrace : WordTrace (prefixWord ++ tailWord_7030583) baseStart_7030583 baseEnd_7030583 := by
    simpa [prefixWord, tailWord_7030583, baseEnd_7030583] using wordTrace_append hprefix tailTrace_7030583
  have hstable : (prefixWord ++ tailWord_7030583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030583).length < 2 ^ (prefixWord ++ tailWord_7030583).sum := by decide
  have hdescent : baseEnd_7030583 < baseStart_7030583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030590 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_7030590 : Nat := 118140960795 + 7030590 * 2 ^ 59
def prefixEnd_7030590 : Nat := 4983230072969 + 3 ^ 40 * 7030590 * 2
def baseEnd_7030590 : Nat := 3610071954693753017991911

theorem tailTrace_7030590 : CollatzResearch.WordTrace tailWord_7030590 prefixEnd_7030590 3610071954693753017991911 := by
  unfold tailWord_7030590
  simp only [CollatzResearch.WordTrace]
  refine ⟨32053335449922579252772153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170951122399587089348118149 32053335449922579252772153)
  ·
    refine ⟨24040001587441934439579115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32053335449922579252772153 24040001587441934439579115)
    ·
      refine ⟨36060002381162901659368673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24040001587441934439579115 36060002381162901659368673)
      ·
        refine ⟨27045001785872176244526505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36060002381162901659368673 27045001785872176244526505)
        ·
          refine ⟨20283751339404132183394879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27045001785872176244526505 20283751339404132183394879)
          ·
            refine ⟨30425627009106198275092319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20283751339404132183394879 30425627009106198275092319)
            ·
              refine ⟨45638440513659297412638479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30425627009106198275092319 45638440513659297412638479)
              ·
                refine ⟨68457660770488946118957719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45638440513659297412638479 68457660770488946118957719)
                ·
                  refine ⟨102686491155733419178436579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68457660770488946118957719 102686491155733419178436579)
                  ·
                    refine ⟨154029736733600128767654869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102686491155733419178436579 154029736733600128767654869)
                    ·
                      refine ⟨3610071954693753017991911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154029736733600128767654869 3610071954693753017991911)
                      ·
                        rfl

theorem cell23_7030590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_7030590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030590 prefixEnd_7030590 := by exact prefixLift 7030590
  have htrace : WordTrace (prefixWord ++ tailWord_7030590) baseStart_7030590 baseEnd_7030590 := by
    simpa [prefixWord, tailWord_7030590, baseEnd_7030590] using wordTrace_append hprefix tailTrace_7030590
  have hstable : (prefixWord ++ tailWord_7030590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030590).length < 2 ^ (prefixWord ++ tailWord_7030590).sum := by decide
  have hdescent : baseEnd_7030590 < baseStart_7030590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030637 : List Nat := [1, 5, 1, 1, 1, 1, 4, 2, 2, 2, 3]
def baseStart_7030637 : Nat := 118140960795 + 7030637 * 2 ^ 59
def prefixEnd_7030637 : Nat := 4983230072969 + 3 ^ 40 * 7030637 * 2
def baseEnd_7030637 : Nat := 3610096088284514334104195

theorem tailTrace_7030637 : CollatzResearch.WordTrace tailWord_7030637 prefixEnd_7030637 3610096088284514334104195 := by
  unfold tailWord_7030637
  simp only [CollatzResearch.WordTrace]
  refine ⟨256428397830210361049138165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170952265220140240699425443 256428397830210361049138165)
  ·
    refine ⟨24040162296582221348356703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 256428397830210361049138165 24040162296582221348356703)
    ·
      refine ⟨36060243444873332022535055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24040162296582221348356703 36060243444873332022535055)
      ·
        refine ⟨54090365167309998033802583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36060243444873332022535055 54090365167309998033802583)
        ·
          refine ⟨81135547750964997050703875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54090365167309998033802583 81135547750964997050703875)
          ·
            refine ⟨121703321626447495576055813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81135547750964997050703875 121703321626447495576055813)
            ·
              refine ⟨22819372804958905420510465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121703321626447495576055813 22819372804958905420510465)
              ·
                refine ⟨17114529603719179065382849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22819372804958905420510465 17114529603719179065382849)
                ·
                  refine ⟨12835897202789384299037137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17114529603719179065382849 12835897202789384299037137)
                  ·
                    refine ⟨9626922902092038224277853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12835897202789384299037137 9626922902092038224277853)
                    ·
                      refine ⟨3610096088284514334104195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9626922902092038224277853 3610096088284514334104195)
                      ·
                        rfl

theorem cell23_7030637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_7030637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030637 prefixEnd_7030637 := by exact prefixLift 7030637
  have htrace : WordTrace (prefixWord ++ tailWord_7030637) baseStart_7030637 baseEnd_7030637 := by
    simpa [prefixWord, tailWord_7030637, baseEnd_7030637] using wordTrace_append hprefix tailTrace_7030637
  have hstable : (prefixWord ++ tailWord_7030637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030637).length < 2 ^ (prefixWord ++ tailWord_7030637).sum := by decide
  have hdescent : baseEnd_7030637 < baseStart_7030637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030643 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 6]
def baseStart_7030643 : Nat := 118140960795 + 7030643 * 2 ^ 59
def prefixEnd_7030643 : Nat := 4983230072969 + 3 ^ 40 * 7030643 * 2
def baseEnd_7030643 : Nat := 3610099169168441310629167

theorem tailTrace_7030643 : CollatzResearch.WordTrace tailWord_7030643 prefixEnd_7030643 3610099169168441310629167 := by
  unfold tailWord_7030643
  simp only [CollatzResearch.WordTrace]
  refine ⟨256428616668188624073856583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170952411112125749382571055 256428616668188624073856583)
  ·
    refine ⟨384642925002282936110784875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256428616668188624073856583 384642925002282936110784875)
    ·
      refine ⟨576964387503424404166177313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384642925002282936110784875 576964387503424404166177313)
      ·
        refine ⟨432723290627568303124632985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 576964387503424404166177313 432723290627568303124632985)
        ·
          refine ⟨324542467970676227343474739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 432723290627568303124632985 324542467970676227343474739)
          ·
            refine ⟨486813701956014341015212109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324542467970676227343474739 486813701956014341015212109)
            ·
              refine ⟨182555138233505377880704541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 486813701956014341015212109 182555138233505377880704541)
              ·
                refine ⟨68458176837564516705264203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182555138233505377880704541 68458176837564516705264203)
                ·
                  refine ⟨102687265256346775057896305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68458176837564516705264203 102687265256346775057896305)
                  ·
                    refine ⟨77015448942260081293422229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102687265256346775057896305 77015448942260081293422229)
                    ·
                      refine ⟨3610099169168441310629167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77015448942260081293422229 3610099169168441310629167)
                      ·
                        rfl

theorem cell23_7030643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_7030643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030643 prefixEnd_7030643 := by exact prefixLift 7030643
  have htrace : WordTrace (prefixWord ++ tailWord_7030643) baseStart_7030643 baseEnd_7030643 := by
    simpa [prefixWord, tailWord_7030643, baseEnd_7030643] using wordTrace_append hprefix tailTrace_7030643
  have hstable : (prefixWord ++ tailWord_7030643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030643).length < 2 ^ (prefixWord ++ tailWord_7030643).sum := by decide
  have hdescent : baseEnd_7030643 < baseStart_7030643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030677 : List Nat := [1, 3, 2, 1, 1, 3, 3, 1, 1, 5, 2]
def baseStart_7030677 : Nat := 118140960795 + 7030677 * 2 ^ 59
def prefixEnd_7030677 : Nat := 4983230072969 + 3 ^ 40 * 7030677 * 2
def baseEnd_7030677 : Nat := 3610116627510694177604011

theorem tailTrace_7030677 : CollatzResearch.WordTrace tailWord_7030677 prefixEnd_7030677 3610116627510694177604011 := by
  unfold tailWord_7030677
  simp only [CollatzResearch.WordTrace]
  refine ⟨256429856750065447880594285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170953237833376965253729523 256429856750065447880594285)
  ·
    refine ⟨96161196281274542955222857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256429856750065447880594285 96161196281274542955222857)
    ·
      refine ⟨72120897210955907216417143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96161196281274542955222857 72120897210955907216417143)
      ·
        refine ⟨108181345816433860824625715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72120897210955907216417143 108181345816433860824625715)
        ·
          refine ⟨162272018724650791236938573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108181345816433860824625715 162272018724650791236938573)
          ·
            refine ⟨60852007021744046713851965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162272018724650791236938573 60852007021744046713851965)
            ·
              refine ⟨22819502633154017517694487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60852007021744046713851965 22819502633154017517694487)
              ·
                refine ⟨34229253949731026276541731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22819502633154017517694487 34229253949731026276541731)
                ·
                  refine ⟨51343880924596539414812597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34229253949731026276541731 51343880924596539414812597)
                  ·
                    refine ⟨4813488836680925570138681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51343880924596539414812597 4813488836680925570138681)
                    ·
                      refine ⟨3610116627510694177604011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4813488836680925570138681 3610116627510694177604011)
                      ·
                        rfl

theorem cell23_7030677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 5, 2].length) (baseStart_7030677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030677 prefixEnd_7030677 := by exact prefixLift 7030677
  have htrace : WordTrace (prefixWord ++ tailWord_7030677) baseStart_7030677 baseEnd_7030677 := by
    simpa [prefixWord, tailWord_7030677, baseEnd_7030677] using wordTrace_append hprefix tailTrace_7030677
  have hstable : (prefixWord ++ tailWord_7030677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030677).length < 2 ^ (prefixWord ++ tailWord_7030677).sum := by decide
  have hdescent : baseEnd_7030677 < baseStart_7030677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030717 : List Nat := [1, 4, 1, 2, 3, 1, 3, 1, 1, 6]
def baseStart_7030717 : Nat := 118140960795 + 7030717 * 2 ^ 59
def prefixEnd_7030717 : Nat := 4983230072969 + 3 ^ 40 * 7030717 * 2
def baseEnd_7030717 : Nat := 1203379055578958007034609

theorem tailTrace_7030717 : CollatzResearch.WordTrace tailWord_7030717 prefixEnd_7030717 1203379055578958007034609 := by
  unfold tailWord_7030717
  simp only [CollatzResearch.WordTrace]
  refine ⟨256431315669920534712050405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170954210446613689808033603 256431315669920534712050405)
  ·
    refine ⟨48080871688110100258509451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256431315669920534712050405 48080871688110100258509451)
    ·
      refine ⟨72121307532165150387764177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48080871688110100258509451 72121307532165150387764177)
      ·
        refine ⟨54090980649123862790823133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72121307532165150387764177 54090980649123862790823133)
        ·
          refine ⟨20284117743421448546558675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54090980649123862790823133 20284117743421448546558675)
          ·
            refine ⟨30426176615132172819838013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20284117743421448546558675 30426176615132172819838013)
            ·
              refine ⟨11409816230674564807439255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30426176615132172819838013 11409816230674564807439255)
              ·
                refine ⟨17114724346011847211158883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11409816230674564807439255 17114724346011847211158883)
                ·
                  refine ⟨25672086519017770816738325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17114724346011847211158883 25672086519017770816738325)
                  ·
                    refine ⟨1203379055578958007034609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25672086519017770816738325 1203379055578958007034609)
                    ·
                      rfl

theorem cell23_7030717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_7030717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030717 prefixEnd_7030717 := by exact prefixLift 7030717
  have htrace : WordTrace (prefixWord ++ tailWord_7030717) baseStart_7030717 baseEnd_7030717 := by
    simpa [prefixWord, tailWord_7030717, baseEnd_7030717] using wordTrace_append hprefix tailTrace_7030717
  have hstable : (prefixWord ++ tailWord_7030717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030717).length < 2 ^ (prefixWord ++ tailWord_7030717).sum := by decide
  have hdescent : baseEnd_7030717 < baseStart_7030717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030720 : List Nat := [2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 6]
def baseStart_7030720 : Nat := 118140960795 + 7030720 * 2 ^ 59
def prefixEnd_7030720 : Nat := 4983230072969 + 3 ^ 40 * 7030720 * 2
def baseEnd_7030720 : Nat := 3610138707178837509366313

theorem tailTrace_7030720 : CollatzResearch.WordTrace tailWord_7030720 prefixEnd_7030720 3610138707178837509366313 := by
  unfold tailWord_7030720
  simp only [CollatzResearch.WordTrace]
  refine ⟨128215712544454833112204807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170954283392606444149606409 128215712544454833112204807)
  ·
    refine ⟨192323568816682249668307211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128215712544454833112204807 192323568816682249668307211)
    ·
      refine ⟨288485353225023374502460817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192323568816682249668307211 288485353225023374502460817)
      ·
        refine ⟨216364014918767530876845613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288485353225023374502460817 216364014918767530876845613)
        ·
          refine ⟨81136505594537824078817105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216364014918767530876845613 81136505594537824078817105)
          ·
            refine ⟨60852379195903368059112829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81136505594537824078817105 60852379195903368059112829)
            ·
              refine ⟨22819642198463763022167311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60852379195903368059112829 22819642198463763022167311)
              ·
                refine ⟨34229463297695644533250967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22819642198463763022167311 34229463297695644533250967)
                ·
                  refine ⟨51344194946543466799876451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34229463297695644533250967 51344194946543466799876451)
                  ·
                    refine ⟨77016292419815200199814677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51344194946543466799876451 77016292419815200199814677)
                    ·
                      refine ⟨3610138707178837509366313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77016292419815200199814677 3610138707178837509366313)
                      ·
                        rfl

theorem cell23_7030720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_7030720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030720 prefixEnd_7030720 := by exact prefixLift 7030720
  have htrace : WordTrace (prefixWord ++ tailWord_7030720) baseStart_7030720 baseEnd_7030720 := by
    simpa [prefixWord, tailWord_7030720, baseEnd_7030720] using wordTrace_append hprefix tailTrace_7030720
  have hstable : (prefixWord ++ tailWord_7030720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030720).length < 2 ^ (prefixWord ++ tailWord_7030720).sum := by decide
  have hdescent : baseEnd_7030720 < baseStart_7030720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030760 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 2, 7]
def baseStart_7030760 : Nat := 118140960795 + 7030760 * 2 ^ 59
def prefixEnd_7030760 : Nat := 4983230072969 + 3 ^ 40 * 7030760 * 2
def baseEnd_7030760 : Nat := 1203386415468339117622043

theorem tailTrace_7030760 : CollatzResearch.WordTrace tailWord_7030760 prefixEnd_7030760 1203386415468339117622043 := by
  unfold tailWord_7030760
  simp only [CollatzResearch.WordTrace]
  refine ⟨128216442004382376527932867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170955256005843168703910489 128216442004382376527932867)
  ·
    refine ⟨192324663006573564791899301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128216442004382376527932867 192324663006573564791899301)
    ·
      refine ⟨36060874313732543398481119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192324663006573564791899301 36060874313732543398481119)
      ·
        refine ⟨54091311470598815097721679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36060874313732543398481119 54091311470598815097721679)
        ·
          refine ⟨81136967205898222646582519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54091311470598815097721679 81136967205898222646582519)
          ·
            refine ⟨121705450808847333969873779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81136967205898222646582519 121705450808847333969873779)
            ·
              refine ⟨182558176213271000954810669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121705450808847333969873779 182558176213271000954810669)
              ·
                refine ⟨68459316079976625358054001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182558176213271000954810669 68459316079976625358054001)
                ·
                  refine ⟨51344487059982469018540501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68459316079976625358054001 51344487059982469018540501)
                  ·
                    refine ⟨1203386415468339117622043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51344487059982469018540501 1203386415468339117622043)
                    ·
                      rfl

theorem cell23_7030760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_7030760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030760 prefixEnd_7030760 := by exact prefixLift 7030760
  have htrace : WordTrace (prefixWord ++ tailWord_7030760) baseStart_7030760 baseEnd_7030760 := by
    simpa [prefixWord, tailWord_7030760, baseEnd_7030760] using wordTrace_append hprefix tailTrace_7030760
  have hstable : (prefixWord ++ tailWord_7030760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030760).length < 2 ^ (prefixWord ++ tailWord_7030760).sum := by decide
  have hdescent : baseEnd_7030760 < baseStart_7030760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030784 : List Nat := [2, 1, 1, 2, 1, 1, 1, 8, 1, 3, 2]
def baseStart_7030784 : Nat := 118140960795 + 7030784 * 2 ^ 59
def prefixEnd_7030784 : Nat := 4983230072969 + 3 ^ 40 * 7030784 * 2
def baseEnd_7030784 : Nat := 3610171569940725258966019

theorem tailTrace_7030784 : CollatzResearch.WordTrace tailWord_7030784 prefixEnd_7030784 3610171569940725258966019 := by
  unfold tailWord_7030784
  simp only [CollatzResearch.WordTrace]
  refine ⟨128216879680338902577369703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170955839573785203436492937 128216879680338902577369703)
  ·
    refine ⟨192325319520508353866054555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128216879680338902577369703 192325319520508353866054555)
    ·
      refine ⟨288487979280762530799081833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192325319520508353866054555 288487979280762530799081833)
      ·
        refine ⟨216365984460571898099311375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288487979280762530799081833 216365984460571898099311375)
        ·
          refine ⟨324548976690857847148967063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216365984460571898099311375 324548976690857847148967063)
          ·
            refine ⟨486823465036286770723450595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324548976690857847148967063 486823465036286770723450595)
            ·
              refine ⟨730235197554430156085175893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486823465036286770723450595 730235197554430156085175893)
              ·
                refine ⟨8557443721340978391623155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 730235197554430156085175893 8557443721340978391623155)
                ·
                  refine ⟨12836165582011467587434733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8557443721340978391623155 12836165582011467587434733)
                  ·
                    refine ⟨4813562093254300345288025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12836165582011467587434733 4813562093254300345288025)
                    ·
                      refine ⟨3610171569940725258966019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4813562093254300345288025 3610171569940725258966019)
                      ·
                        rfl

theorem cell23_7030784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 1, 3, 2].length) (baseStart_7030784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030784 prefixEnd_7030784 := by exact prefixLift 7030784
  have htrace : WordTrace (prefixWord ++ tailWord_7030784) baseStart_7030784 baseEnd_7030784 := by
    simpa [prefixWord, tailWord_7030784, baseEnd_7030784] using wordTrace_append hprefix tailTrace_7030784
  have hstable : (prefixWord ++ tailWord_7030784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030784).length < 2 ^ (prefixWord ++ tailWord_7030784).sum := by decide
  have hdescent : baseEnd_7030784 < baseStart_7030784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030854 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 9]
def baseStart_7030854 : Nat := 118140960795 + 7030854 * 2 ^ 59
def prefixEnd_7030854 : Nat := 4983230072969 + 3 ^ 40 * 7030854 * 2
def baseEnd_7030854 : Nat := 401134168176282220565633

theorem tailTrace_7030854 : CollatzResearch.WordTrace tailWord_7030854 prefixEnd_7030854 401134168176282220565633 := by
  unfold tailWord_7030854
  simp only [CollatzResearch.WordTrace]
  refine ⟨8013634764700756472180863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 170957541646949471406525077 8013634764700756472180863)
  ·
    refine ⟨12020452147051134708271295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8013634764700756472180863 12020452147051134708271295)
    ·
      refine ⟨18030678220576702062406943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12020452147051134708271295 18030678220576702062406943)
      ·
        refine ⟨27046017330865053093610415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18030678220576702062406943 27046017330865053093610415)
        ·
          refine ⟨40569025996297579640415623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27046017330865053093610415 40569025996297579640415623)
          ·
            refine ⟨60853538994446369460623435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40569025996297579640415623 60853538994446369460623435)
            ·
              refine ⟨91280308491669554190935153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60853538994446369460623435 91280308491669554190935153)
              ·
                refine ⟨68460231368752165643201365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91280308491669554190935153 68460231368752165643201365)
                ·
                  refine ⟨401134168176282220565633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68460231368752165643201365 401134168176282220565633)
                  ·
                    rfl

theorem cell23_7030854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_7030854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030854 prefixEnd_7030854 := by exact prefixLift 7030854
  have htrace : WordTrace (prefixWord ++ tailWord_7030854) baseStart_7030854 baseEnd_7030854 := by
    simpa [prefixWord, tailWord_7030854, baseEnd_7030854] using wordTrace_append hprefix tailTrace_7030854
  have hstable : (prefixWord ++ tailWord_7030854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030854).length < 2 ^ (prefixWord ++ tailWord_7030854).sum := by decide
  have hdescent : baseEnd_7030854 < baseStart_7030854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030882 : List Nat := [3, 3, 2, 2, 2, 1, 3, 1, 2, 2, 2]
def baseStart_7030882 : Nat := 118140960795 + 7030882 * 2 ^ 59
def prefixEnd_7030882 : Nat := 4983230072969 + 3 ^ 40 * 7030882 * 2
def baseEnd_7030882 : Nat := 3610221891044865875540569

theorem tailTrace_7030882 : CollatzResearch.WordTrace tailWord_7030882 prefixEnd_7030882 3610221891044865875540569 := by
  unfold tailWord_7030882
  simp only [CollatzResearch.WordTrace]
  refine ⟨64109333428580691972951725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170958222476215178594537933 64109333428580691972951725)
  ·
    refine ⟨24041000035717759489856897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64109333428580691972951725 24041000035717759489856897)
    ·
      refine ⟨18030750026788319617392673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24041000035717759489856897 18030750026788319617392673)
      ·
        refine ⟨13523062520091239713044505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18030750026788319617392673 13523062520091239713044505)
        ·
          refine ⟨10142296890068429784783379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13523062520091239713044505 10142296890068429784783379)
          ·
            refine ⟨15213445335102644677175069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10142296890068429784783379 15213445335102644677175069)
            ·
              refine ⟨5705042000663491753940651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15213445335102644677175069 5705042000663491753940651)
              ·
                refine ⟨8557563000995237630910977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5705042000663491753940651 8557563000995237630910977)
                ·
                  refine ⟨6418172250746428223183233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8557563000995237630910977 6418172250746428223183233)
                  ·
                    refine ⟨4813629188059821167387425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6418172250746428223183233 4813629188059821167387425)
                    ·
                      refine ⟨3610221891044865875540569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4813629188059821167387425 3610221891044865875540569)
                      ·
                        rfl

theorem cell23_7030882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_7030882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030882 prefixEnd_7030882 := by exact prefixLift 7030882
  have htrace : WordTrace (prefixWord ++ tailWord_7030882) baseStart_7030882 baseEnd_7030882 := by
    simpa [prefixWord, tailWord_7030882, baseEnd_7030882] using wordTrace_append hprefix tailTrace_7030882
  have hstable : (prefixWord ++ tailWord_7030882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030882).length < 2 ^ (prefixWord ++ tailWord_7030882).sum := by decide
  have hdescent : baseEnd_7030882 < baseStart_7030882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030887 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_7030887 : Nat := 118140960795 + 7030887 * 2 ^ 59
def prefixEnd_7030887 : Nat := 4983230072969 + 3 ^ 40 * 7030887 * 2
def baseEnd_7030887 : Nat := 3610224458448138355978045

theorem tailTrace_7030887 : CollatzResearch.WordTrace tailWord_7030887 prefixEnd_7030887 3610224458448138355978045 := by
  unfold tailWord_7030887
  simp only [CollatzResearch.WordTrace]
  refine ⟨256437516079304653745738915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170958344052869769163825943 256437516079304653745738915)
  ·
    refine ⟨384656274118956980618608373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256437516079304653745738915 384656274118956980618608373)
    ·
      refine ⟨36061525698652216932994535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 384656274118956980618608373 36061525698652216932994535)
      ·
        refine ⟨54092288547978325399491803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36061525698652216932994535 54092288547978325399491803)
        ·
          refine ⟨81138432821967488099237705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54092288547978325399491803 81138432821967488099237705)
          ·
            refine ⟨60853824616475616074428279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81138432821967488099237705 60853824616475616074428279)
            ·
              refine ⟨91280736924713424111642419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60853824616475616074428279 91280736924713424111642419)
              ·
                refine ⟨136921105387070136167463629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91280736924713424111642419 136921105387070136167463629)
                ·
                  refine ⟨51345414520151301062798861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136921105387070136167463629 51345414520151301062798861)
                  ·
                    refine ⟨19254530445056737898549573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51345414520151301062798861 19254530445056737898549573)
                    ·
                      refine ⟨3610224458448138355978045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19254530445056737898549573 3610224458448138355978045)
                      ·
                        rfl

theorem cell23_7030887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_7030887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030887 prefixEnd_7030887 := by exact prefixLift 7030887
  have htrace : WordTrace (prefixWord ++ tailWord_7030887) baseStart_7030887 baseEnd_7030887 := by
    simpa [prefixWord, tailWord_7030887, baseEnd_7030887] using wordTrace_append hprefix tailTrace_7030887
  have hstable : (prefixWord ++ tailWord_7030887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030887).length < 2 ^ (prefixWord ++ tailWord_7030887).sum := by decide
  have hdescent : baseEnd_7030887 < baseStart_7030887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030944 : List Nat := [2, 1, 1, 4, 2, 3, 1, 3, 6]
def baseStart_7030944 : Nat := 118140960795 + 7030944 * 2 ^ 59
def prefixEnd_7030944 : Nat := 4983230072969 + 3 ^ 40 * 7030944 * 2
def baseEnd_7030944 : Nat := 401139302982827181440587

theorem tailTrace_7030944 : CollatzResearch.WordTrace tailWord_7030944 prefixEnd_7030944 401139302982827181440587 := by
  unfold tailWord_7030944
  simp only [CollatzResearch.WordTrace]
  refine ⟨128219797520049076240281943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170959730026732101653709257 128219797520049076240281943)
  ·
    refine ⟨192329696280073614360422915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128219797520049076240281943 192329696280073614360422915)
    ·
      refine ⟨288494544420110421540634373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192329696280073614360422915 288494544420110421540634373)
      ·
        refine ⟨54092727078770704038868945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 288494544420110421540634373 54092727078770704038868945)
        ·
          refine ⟨40569545309078028029151709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54092727078770704038868945 40569545309078028029151709)
          ·
            refine ⟨15213579490904260510931891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40569545309078028029151709 15213579490904260510931891)
            ·
              refine ⟨22820369236356390766397837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15213579490904260510931891 22820369236356390766397837)
              ·
                refine ⟨8557638463633646537399189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22820369236356390766397837 8557638463633646537399189)
                ·
                  refine ⟨401139302982827181440587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8557638463633646537399189 401139302982827181440587)
                  ·
                    rfl

theorem cell23_7030944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 6].length) (baseStart_7030944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030944 prefixEnd_7030944 := by exact prefixLift 7030944
  have htrace : WordTrace (prefixWord ++ tailWord_7030944) baseStart_7030944 baseEnd_7030944 := by
    simpa [prefixWord, tailWord_7030944, baseEnd_7030944] using wordTrace_append hprefix tailTrace_7030944
  have hstable : (prefixWord ++ tailWord_7030944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030944).length < 2 ^ (prefixWord ++ tailWord_7030944).sum := by decide
  have hdescent : baseEnd_7030944 < baseStart_7030944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030978 : List Nat := [3, 5, 1, 1, 1, 1, 1, 4, 6]
def baseStart_7030978 : Nat := 118140960795 + 7030978 * 2 ^ 59
def prefixEnd_7030978 : Nat := 4983230072969 + 3 ^ 40 * 7030978 * 2
def baseEnd_7030978 : Nat := 401141242798633055548903

theorem tailTrace_7030978 : CollatzResearch.WordTrace tailWord_7030978 prefixEnd_7030978 401141242798633055548903 := by
  unfold tailWord_7030978
  simp only [CollatzResearch.WordTrace]
  refine ⟨64110208780493744071825397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170960556747983317524867725 64110208780493744071825397)
  ·
    refine ⟨6010332073171288506733631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64110208780493744071825397 6010332073171288506733631)
    ·
      refine ⟨9015498109756932760100447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6010332073171288506733631 9015498109756932760100447)
      ·
        refine ⟨13523247164635399140150671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9015498109756932760100447 13523247164635399140150671)
        ·
          refine ⟨20284870746953098710226007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13523247164635399140150671 20284870746953098710226007)
          ·
            refine ⟨30427306120429648065339011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20284870746953098710226007 30427306120429648065339011)
            ·
              refine ⟨45640959180644472098008517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30427306120429648065339011 45640959180644472098008517)
              ·
                refine ⟨8557679846370838518376597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45640959180644472098008517 8557679846370838518376597)
                ·
                  refine ⟨401141242798633055548903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8557679846370838518376597 401141242798633055548903)
                  ·
                    rfl

theorem cell23_7030978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_7030978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030978 prefixEnd_7030978 := by exact prefixLift 7030978
  have htrace : WordTrace (prefixWord ++ tailWord_7030978) baseStart_7030978 baseEnd_7030978 := by
    simpa [prefixWord, tailWord_7030978, baseEnd_7030978] using wordTrace_append hprefix tailTrace_7030978
  have hstable : (prefixWord ++ tailWord_7030978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030978).length < 2 ^ (prefixWord ++ tailWord_7030978).sum := by decide
  have hdescent : baseEnd_7030978 < baseStart_7030978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030981 : List Nat := [1, 3, 1, 1, 1, 1, 6, 2, 2, 3, 2]
def baseStart_7030981 : Nat := 118140960795 + 7030981 * 2 ^ 59
def prefixEnd_7030981 : Nat := 4983230072969 + 3 ^ 40 * 7030981 * 2
def baseEnd_7030981 : Nat := 3610272725629660988202613

theorem tailTrace_7030981 : CollatzResearch.WordTrace tailWord_7030981 prefixEnd_7030981 3610272725629660988202613 := by
  unfold tailWord_7030981
  simp only [CollatzResearch.WordTrace]
  refine ⟨256440944540964107799660797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170960629693976071866440531 256440944540964107799660797)
  ·
    refine ⟨96165354202861540424872799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256440944540964107799660797 96165354202861540424872799)
    ·
      refine ⟨144248031304292310637309199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96165354202861540424872799 144248031304292310637309199)
      ·
        refine ⟨216372046956438465955963799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144248031304292310637309199 216372046956438465955963799)
        ·
          refine ⟨324558070434657698933945699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216372046956438465955963799 324558070434657698933945699)
          ·
            refine ⟨486837105651986548400918549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324558070434657698933945699 486837105651986548400918549)
            ·
              refine ⟨22820489327436869456293057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 486837105651986548400918549 22820489327436869456293057)
              ·
                refine ⟨17115366995577652092219793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22820489327436869456293057 17115366995577652092219793)
                ·
                  refine ⟨12836525246683239069164845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17115366995577652092219793 12836525246683239069164845)
                  ·
                    refine ⟨4813696967506214650936817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12836525246683239069164845 4813696967506214650936817)
                    ·
                      refine ⟨3610272725629660988202613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4813696967506214650936817 3610272725629660988202613)
                      ·
                        rfl

theorem cell23_7030981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 3, 2].length) (baseStart_7030981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030981 prefixEnd_7030981 := by exact prefixLift 7030981
  have htrace : WordTrace (prefixWord ++ tailWord_7030981) baseStart_7030981 baseEnd_7030981 := by
    simpa [prefixWord, tailWord_7030981, baseEnd_7030981] using wordTrace_append hprefix tailTrace_7030981
  have hstable : (prefixWord ++ tailWord_7030981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030981).length < 2 ^ (prefixWord ++ tailWord_7030981).sum := by decide
  have hdescent : baseEnd_7030981 < baseStart_7030981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7030987 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 3, 6]
def baseStart_7030987 : Nat := 118140960795 + 7030987 * 2 ^ 59
def prefixEnd_7030987 : Nat := 4983230072969 + 3 ^ 40 * 7030987 * 2
def baseEnd_7030987 : Nat := 1203425268837862654909195

theorem tailTrace_7030987 : CollatzResearch.WordTrace tailWord_7030987 prefixEnd_7030987 1203425268837862654909195 := by
  unfold tailWord_7030987
  simp only [CollatzResearch.WordTrace]
  refine ⟨256441163378942370824379215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170960775585961580549586143 256441163378942370824379215)
  ·
    refine ⟨384661745068413556236568823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256441163378942370824379215 384661745068413556236568823)
    ·
      refine ⟨576992617602620334354853235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384661745068413556236568823 576992617602620334354853235)
      ·
        refine ⟨865488926403930501532279853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576992617602620334354853235 865488926403930501532279853)
        ·
          refine ⟨324558347401473938074604945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 865488926403930501532279853 324558347401473938074604945)
          ·
            refine ⟨243418760551105453555953709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324558347401473938074604945 243418760551105453555953709)
            ·
              refine ⟨91282035206664545083482641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243418760551105453555953709 91282035206664545083482641)
              ·
                refine ⟨68461526404998408812611981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91282035206664545083482641 68461526404998408812611981)
                ·
                  refine ⟨25673072401874403304729493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68461526404998408812611981 25673072401874403304729493)
                  ·
                    refine ⟨1203425268837862654909195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25673072401874403304729493 1203425268837862654909195)
                    ·
                      rfl

theorem cell23_7030987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 6].length) (baseStart_7030987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7030987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7030987 prefixEnd_7030987 := by exact prefixLift 7030987
  have htrace : WordTrace (prefixWord ++ tailWord_7030987) baseStart_7030987 baseEnd_7030987 := by
    simpa [prefixWord, tailWord_7030987, baseEnd_7030987] using wordTrace_append hprefix tailTrace_7030987
  have hstable : (prefixWord ++ tailWord_7030987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7030987).length < 2 ^ (prefixWord ++ tailWord_7030987).sum := by decide
  have hdescent : baseEnd_7030987 < baseStart_7030987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7030987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031015 : List Nat := [1, 1, 5, 3, 1, 3, 1, 1, 2, 3, 2]
def baseStart_7031015 : Nat := 118140960795 + 7031015 * 2 ^ 59
def prefixEnd_7031015 : Nat := 4983230072969 + 3 ^ 40 * 7031015 * 2
def baseEnd_7031015 : Nat := 3610290183971913855177457

theorem tailTrace_7031015 : CollatzResearch.WordTrace tailWord_7031015 prefixEnd_7031015 3610290183971913855177457 := by
  unfold tailWord_7031015
  simp only [CollatzResearch.WordTrace]
  refine ⟨256442184622840931606398499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170961456415227287737598999 256442184622840931606398499)
  ·
    refine ⟨384663276934261397409597749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256442184622840931606398499 384663276934261397409597749)
    ·
      refine ⟨36062182212587006007149789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 384663276934261397409597749 36062182212587006007149789)
      ·
        refine ⟨13523318329720127252681171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36062182212587006007149789 13523318329720127252681171)
        ·
          refine ⟨20284977494580190879021757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13523318329720127252681171 20284977494580190879021757)
          ·
            refine ⟨7606866560467571579633159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20284977494580190879021757 7606866560467571579633159)
            ·
              refine ⟨11410299840701357369449739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7606866560467571579633159 11410299840701357369449739)
              ·
                refine ⟨17115449761052036054174609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11410299840701357369449739 17115449761052036054174609)
                ·
                  refine ⟨12836587320789027040630957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17115449761052036054174609 12836587320789027040630957)
                  ·
                    refine ⟨4813720245295885140236609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12836587320789027040630957 4813720245295885140236609)
                    ·
                      refine ⟨3610290183971913855177457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4813720245295885140236609 3610290183971913855177457)
                      ·
                        rfl

theorem cell23_7031015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_7031015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031015 prefixEnd_7031015 := by exact prefixLift 7031015
  have htrace : WordTrace (prefixWord ++ tailWord_7031015) baseStart_7031015 baseEnd_7031015 := by
    simpa [prefixWord, tailWord_7031015, baseEnd_7031015] using wordTrace_append hprefix tailTrace_7031015
  have hstable : (prefixWord ++ tailWord_7031015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031015).length < 2 ^ (prefixWord ++ tailWord_7031015).sum := by decide
  have hdescent : baseEnd_7031015 < baseStart_7031015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031061 : List Nat := [1, 3, 2, 1, 2, 1, 5, 1, 1, 3, 3]
def baseStart_7031061 : Nat := 118140960795 + 7031061 * 2 ^ 59
def prefixEnd_7031061 : Nat := 4983230072969 + 3 ^ 40 * 7031061 * 2
def baseEnd_7031061 : Nat := 3610313804082020675202245

theorem tailTrace_7031061 : CollatzResearch.WordTrace tailWord_7031061 prefixEnd_7031061 3610313804082020675202245 := by
  unfold tailWord_7031061
  simp only [CollatzResearch.WordTrace]
  refine ⟨256443862380674281462573037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170962574920449520975048691 256443862380674281462573037)
  ·
    refine ⟨96166448392752855548464889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256443862380674281462573037 96166448392752855548464889)
    ·
      refine ⟨72124836294564641661348667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96166448392752855548464889 72124836294564641661348667)
      ·
        refine ⟨108187254441846962492023001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72124836294564641661348667 108187254441846962492023001)
        ·
          refine ⟨81140440831385221869017251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108187254441846962492023001 81140440831385221869017251)
          ·
            refine ⟨121710661247077832803525877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81140440831385221869017251 121710661247077832803525877)
            ·
              refine ⟨11410374491913546825330551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121710661247077832803525877 11410374491913546825330551)
              ·
                refine ⟨17115561737870320237995827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11410374491913546825330551 17115561737870320237995827)
                ·
                  refine ⟨25673342606805480356993741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17115561737870320237995827 25673342606805480356993741)
                  ·
                    refine ⟨9627503477552055133872653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25673342606805480356993741 9627503477552055133872653)
                    ·
                      refine ⟨3610313804082020675202245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9627503477552055133872653 3610313804082020675202245)
                      ·
                        rfl

theorem cell23_7031061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_7031061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031061 prefixEnd_7031061 := by exact prefixLift 7031061
  have htrace : WordTrace (prefixWord ++ tailWord_7031061) baseStart_7031061 baseEnd_7031061 := by
    simpa [prefixWord, tailWord_7031061, baseEnd_7031061] using wordTrace_append hprefix tailTrace_7031061
  have hstable : (prefixWord ++ tailWord_7031061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031061).length < 2 ^ (prefixWord ++ tailWord_7031061).sum := by decide
  have hdescent : baseEnd_7031061 < baseStart_7031061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031118 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2]
def baseStart_7031118 : Nat := 118140960795 + 7031118 * 2 ^ 59
def prefixEnd_7031118 : Nat := 4983230072969 + 3 ^ 40 * 7031118 * 2
def baseEnd_7031118 : Nat := 3610343072479326952189483

theorem tailTrace_7031118 : CollatzResearch.WordTrace tailWord_7031118 prefixEnd_7031118 3610343072479326952189483 := by
  unfold tailWord_7031118
  simp only [CollatzResearch.WordTrace]
  refine ⟨32055742667683472524674751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170963960894311853464932005 32055742667683472524674751)
  ·
    refine ⟨48083614001525208787012127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32055742667683472524674751 48083614001525208787012127)
    ·
      refine ⟨72125421002287813180518191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48083614001525208787012127 72125421002287813180518191)
      ·
        refine ⟨108188131503431719770777287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72125421002287813180518191 108188131503431719770777287)
        ·
          refine ⟨162282197255147579656165931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108188131503431719770777287 162282197255147579656165931)
          ·
            refine ⟨243423295882721369484248897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162282197255147579656165931 243423295882721369484248897)
            ·
              refine ⟨182567471912041027113186673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243423295882721369484248897 182567471912041027113186673)
              ·
                refine ⟨136925603934030770334890005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182567471912041027113186673 136925603934030770334890005)
                ·
                  refine ⟨6418387684407692359447969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 136925603934030770334890005 6418387684407692359447969)
                  ·
                    refine ⟨4813790763305769269585977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6418387684407692359447969 4813790763305769269585977)
                    ·
                      refine ⟨3610343072479326952189483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4813790763305769269585977 3610343072479326952189483)
                      ·
                        rfl

theorem cell23_7031118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2].length) (baseStart_7031118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031118 prefixEnd_7031118 := by exact prefixLift 7031118
  have htrace : WordTrace (prefixWord ++ tailWord_7031118) baseStart_7031118 baseEnd_7031118 := by
    simpa [prefixWord, tailWord_7031118, baseEnd_7031118] using wordTrace_append hprefix tailTrace_7031118
  have hstable : (prefixWord ++ tailWord_7031118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031118).length < 2 ^ (prefixWord ++ tailWord_7031118).sum := by decide
  have hdescent : baseEnd_7031118 < baseStart_7031118 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031164 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 1, 1, 7]
def baseStart_7031164 : Nat := 118140960795 + 7031164 * 2 ^ 59
def prefixEnd_7031164 : Nat := 4983230072969 + 3 ^ 40 * 7031164 * 2
def baseEnd_7031164 : Nat := 3610366692589433772214271

theorem tailTrace_7031164 : CollatzResearch.WordTrace tailWord_7031164 prefixEnd_7031164 3610366692589433772214271 := by
  unfold tailWord_7031164
  simp only [CollatzResearch.WordTrace]
  refine ⟨128223809549650565026786273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170965079399534086702381697 128223809549650565026786273)
  ·
    refine ⟨96167857162237923770089705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128223809549650565026786273 96167857162237923770089705)
    ·
      refine ⟨72125892871678442827567279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96167857162237923770089705 72125892871678442827567279)
      ·
        refine ⟨108188839307517664241350919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72125892871678442827567279 108188839307517664241350919)
        ·
          refine ⟨162283258961276496362026379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108188839307517664241350919 162283258961276496362026379)
          ·
            refine ⟨243424888441914744543039569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162283258961276496362026379 243424888441914744543039569)
            ·
              refine ⟨182568666331436058407279677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243424888441914744543039569 182568666331436058407279677)
              ·
                refine ⟨68463249874288521902729879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182568666331436058407279677 68463249874288521902729879)
                ·
                  refine ⟨102694874811432782854094819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68463249874288521902729879 102694874811432782854094819)
                  ·
                    refine ⟨154042312217149174281142229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102694874811432782854094819 154042312217149174281142229)
                    ·
                      refine ⟨3610366692589433772214271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154042312217149174281142229 3610366692589433772214271)
                      ·
                        rfl

theorem cell23_7031164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_7031164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031164 prefixEnd_7031164 := by exact prefixLift 7031164
  have htrace : WordTrace (prefixWord ++ tailWord_7031164) baseStart_7031164 baseEnd_7031164 := by
    simpa [prefixWord, tailWord_7031164, baseEnd_7031164] using wordTrace_append hprefix tailTrace_7031164
  have hstable : (prefixWord ++ tailWord_7031164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031164).length < 2 ^ (prefixWord ++ tailWord_7031164).sum := by decide
  have hdescent : baseEnd_7031164 < baseStart_7031164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031188 : List Nat := [2, 4, 2, 1, 3, 1, 1, 1, 1, 7]
def baseStart_7031188 : Nat := 118140960795 + 7031188 * 2 ^ 59
def prefixEnd_7031188 : Nat := 4983230072969 + 3 ^ 40 * 7031188 * 2
def baseEnd_7031188 : Nat := 1203459672041713892771387

theorem tailTrace_7031188 : CollatzResearch.WordTrace tailWord_7031188 prefixEnd_7031188 1203459672041713892771387 := by
  unfold tailWord_7031188
  simp only [CollatzResearch.WordTrace]
  refine ⟨128224247225607091076223109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170965662967476121434964145 128224247225607091076223109)
  ·
    refine ⟨24042046354801329576791833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128224247225607091076223109 24042046354801329576791833)
    ·
      refine ⟨18031534766100997182593875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24042046354801329576791833 18031534766100997182593875)
      ·
        refine ⟨27047302149151495773890813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18031534766100997182593875 27047302149151495773890813)
        ·
          refine ⟨10142738305931810915209055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27047302149151495773890813 10142738305931810915209055)
          ·
            refine ⟨15214107458897716372813583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10142738305931810915209055 15214107458897716372813583)
            ·
              refine ⟨22821161188346574559220375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15214107458897716372813583 22821161188346574559220375)
              ·
                refine ⟨34231741782519861838830563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22821161188346574559220375 34231741782519861838830563)
                ·
                  refine ⟨51347612673779792758245845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34231741782519861838830563 51347612673779792758245845)
                  ·
                    refine ⟨1203459672041713892771387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51347612673779792758245845 1203459672041713892771387)
                    ·
                      rfl

theorem cell23_7031188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_7031188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031188 prefixEnd_7031188 := by exact prefixLift 7031188
  have htrace : WordTrace (prefixWord ++ tailWord_7031188) baseStart_7031188 baseEnd_7031188 := by
    simpa [prefixWord, tailWord_7031188, baseEnd_7031188] using wordTrace_append hprefix tailTrace_7031188
  have hstable : (prefixWord ++ tailWord_7031188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031188).length < 2 ^ (prefixWord ++ tailWord_7031188).sum := by decide
  have hdescent : baseEnd_7031188 < baseStart_7031188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031190 : List Nat := [5, 3, 1, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_7031190 : Nat := 118140960795 + 7031190 * 2 ^ 59
def prefixEnd_7031190 : Nat := 4983230072969 + 3 ^ 40 * 7031190 * 2
def baseEnd_7031190 : Nat := 3610380043086450670489153

theorem tailTrace_7031190 : CollatzResearch.WordTrace tailWord_7031190 prefixEnd_7031190 3610380043086450670489153 := by
  unfold tailWord_7031190
  simp only [CollatzResearch.WordTrace]
  refine ⟨16028035462325433530876189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170965711598137957662679349 16028035462325433530876189)
  ·
    refine ⟨6010513298372037574078571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16028035462325433530876189 6010513298372037574078571)
    ·
      refine ⟨9015769947558056361117857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6010513298372037574078571 9015769947558056361117857)
      ·
        refine ⟨6761827460668542270838393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9015769947558056361117857 6761827460668542270838393)
        ·
          refine ⟨5071370595501406703128795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6761827460668542270838393 5071370595501406703128795)
          ·
            refine ⟨7607055893252110054693193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5071370595501406703128795 7607055893252110054693193)
            ·
              refine ⟨5705291919939082541019895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7607055893252110054693193 5705291919939082541019895)
              ·
                refine ⟨8557937879908623811529843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5705291919939082541019895 8557937879908623811529843)
                ·
                  refine ⟨12836906819862935717294765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8557937879908623811529843 12836906819862935717294765)
                  ·
                    refine ⟨4813840057448600893985537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12836906819862935717294765 4813840057448600893985537)
                    ·
                      refine ⟨3610380043086450670489153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4813840057448600893985537 3610380043086450670489153)
                      ·
                        rfl

theorem cell23_7031190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_7031190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031190 prefixEnd_7031190 := by exact prefixLift 7031190
  have htrace : WordTrace (prefixWord ++ tailWord_7031190) baseStart_7031190 baseEnd_7031190 := by
    simpa [prefixWord, tailWord_7031190, baseEnd_7031190] using wordTrace_append hprefix tailTrace_7031190
  have hstable : (prefixWord ++ tailWord_7031190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031190).length < 2 ^ (prefixWord ++ tailWord_7031190).sum := by decide
  have hdescent : baseEnd_7031190 < baseStart_7031190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031218 : List Nat := [3, 2, 1, 1, 1, 1, 6, 1, 3, 4]
def baseStart_7031218 : Nat := 118140960795 + 7031218 * 2 ^ 59
def prefixEnd_7031218 : Nat := 4983230072969 + 3 ^ 40 * 7031218 * 2
def baseEnd_7031218 : Nat := 1203464806848258853646341

theorem tailTrace_7031218 : CollatzResearch.WordTrace tailWord_7031218 prefixEnd_7031218 1203464806848258853646341 := by
  unfold tailWord_7031218
  simp only [CollatzResearch.WordTrace]
  refine ⟨64112397160276374319009577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170966392427403664850692205 64112397160276374319009577)
  ·
    refine ⟨48084297870207280739257183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64112397160276374319009577 48084297870207280739257183)
    ·
      refine ⟨72126446805310921108885775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48084297870207280739257183 72126446805310921108885775)
      ·
        refine ⟨108189670207966381663328663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72126446805310921108885775 108189670207966381663328663)
        ·
          refine ⟨162284505311949572494992995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108189670207966381663328663 162284505311949572494992995)
          ·
            refine ⟨243426757967924358742489493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162284505311949572494992995 243426757967924358742489493)
            ·
              refine ⟨11410629279746454316054195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 243426757967924358742489493 11410629279746454316054195)
              ·
                refine ⟨17115943919619681474081293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11410629279746454316054195 17115943919619681474081293)
                ·
                  refine ⟨6418478969857380552780485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17115943919619681474081293 6418478969857380552780485)
                  ·
                    refine ⟨1203464806848258853646341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6418478969857380552780485 1203464806848258853646341)
                    ·
                      rfl

theorem cell23_7031218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_7031218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031218 prefixEnd_7031218 := by exact prefixLift 7031218
  have htrace : WordTrace (prefixWord ++ tailWord_7031218) baseStart_7031218 baseEnd_7031218 := by
    simpa [prefixWord, tailWord_7031218, baseEnd_7031218] using wordTrace_append hprefix tailTrace_7031218
  have hstable : (prefixWord ++ tailWord_7031218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031218).length < 2 ^ (prefixWord ++ tailWord_7031218).sum := by decide
  have hdescent : baseEnd_7031218 < baseStart_7031218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031228 : List Nat := [2, 2, 2, 4, 1, 1, 1, 2, 1, 4, 3]
def baseStart_7031228 : Nat := 118140960795 + 7031228 * 2 ^ 59
def prefixEnd_7031228 : Nat := 4983230072969 + 3 ^ 40 * 7031228 * 2
def baseEnd_7031228 : Nat := 3610399555351321521813977

theorem tailTrace_7031228 : CollatzResearch.WordTrace tailWord_7031228 prefixEnd_7031228 3610399555351321521813977 := by
  unfold tailWord_7031228
  simp only [CollatzResearch.WordTrace]
  refine ⟨128224976685534634491951169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170966635580712845989268225 128224976685534634491951169)
  ·
    refine ⟨96168732514150975868963377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128224976685534634491951169 96168732514150975868963377)
    ·
      refine ⟨72126549385613231901722533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96168732514150975868963377 72126549385613231901722533)
      ·
        refine ⟨13523728009802480981572975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72126549385613231901722533 13523728009802480981572975)
        ·
          refine ⟨20285592014703721472359463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13523728009802480981572975 20285592014703721472359463)
          ·
            refine ⟨30428388022055582208539195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20285592014703721472359463 30428388022055582208539195)
            ·
              refine ⟨45642582033083373312808793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30428388022055582208539195 45642582033083373312808793)
              ·
                refine ⟨34231936524812529984606595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45642582033083373312808793 34231936524812529984606595)
                ·
                  refine ⟨51347904787218794976909893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34231936524812529984606595 51347904787218794976909893)
                  ·
                    refine ⟨9627732147603524058170605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51347904787218794976909893 9627732147603524058170605)
                    ·
                      refine ⟨3610399555351321521813977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9627732147603524058170605 3610399555351321521813977)
                      ·
                        rfl

theorem cell23_7031228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_7031228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031228 prefixEnd_7031228 := by exact prefixLift 7031228
  have htrace : WordTrace (prefixWord ++ tailWord_7031228) baseStart_7031228 baseEnd_7031228 := by
    simpa [prefixWord, tailWord_7031228, baseEnd_7031228] using wordTrace_append hprefix tailTrace_7031228
  have hstable : (prefixWord ++ tailWord_7031228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031228).length < 2 ^ (prefixWord ++ tailWord_7031228).sum := by decide
  have hdescent : baseEnd_7031228 < baseStart_7031228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031252 : List Nat := [2, 4, 1, 2, 2, 1, 3, 3, 1, 4]
def baseStart_7031252 : Nat := 118140960795 + 7031252 * 2 ^ 59
def prefixEnd_7031252 : Nat := 4983230072969 + 3 ^ 40 * 7031252 * 2
def baseEnd_7031252 : Nat := 1203470626295676475971289

theorem tailTrace_7031252 : CollatzResearch.WordTrace tailWord_7031252 prefixEnd_7031252 1203470626295676475971289 := by
  unfold tailWord_7031252
  simp only [CollatzResearch.WordTrace]
  refine ⟨128225414361491160541388005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170967219148654880721850673 128225414361491160541388005)
  ·
    refine ⟨24042265192779592601510251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128225414361491160541388005 24042265192779592601510251)
    ·
      refine ⟨36063397789169388902265377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24042265192779592601510251 36063397789169388902265377)
      ·
        refine ⟨27047548341877041676699033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36063397789169388902265377 27047548341877041676699033)
        ·
          refine ⟨20285661256407781257524275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27047548341877041676699033 20285661256407781257524275)
          ·
            refine ⟨30428491884611671886286413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20285661256407781257524275 30428491884611671886286413)
            ·
              refine ⟨11410684456729376957357405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30428491884611671886286413 11410684456729376957357405)
              ·
                refine ⟨4279006671273516359009027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11410684456729376957357405 4279006671273516359009027)
                ·
                  refine ⟨6418510006910274538513541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4279006671273516359009027 6418510006910274538513541)
                  ·
                    refine ⟨1203470626295676475971289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6418510006910274538513541 1203470626295676475971289)
                    ·
                      rfl

theorem cell23_7031252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_7031252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031252 prefixEnd_7031252 := by exact prefixLift 7031252
  have htrace : WordTrace (prefixWord ++ tailWord_7031252) baseStart_7031252 baseEnd_7031252 := by
    simpa [prefixWord, tailWord_7031252, baseEnd_7031252] using wordTrace_append hprefix tailTrace_7031252
  have hstable : (prefixWord ++ tailWord_7031252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031252).length < 2 ^ (prefixWord ++ tailWord_7031252).sum := by decide
  have hdescent : baseEnd_7031252 < baseStart_7031252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031269 : List Nat := [1, 3, 1, 5, 2, 1, 3, 2, 1, 4]
def baseStart_7031269 : Nat := 118140960795 + 7031269 * 2 ^ 59
def prefixEnd_7031269 : Nat := 4983230072969 + 3 ^ 40 * 7031269 * 2
def baseEnd_7031269 : Nat := 1203473536019385287133763

theorem tailTrace_7031269 : CollatzResearch.WordTrace tailWord_7031269 prefixEnd_7031269 1203473536019385287133763 := by
  unfold tailWord_7031269
  simp only [CollatzResearch.WordTrace]
  refine ⟨256451448763920732986144861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170967632509280488657429907 256451448763920732986144861)
  ·
    refine ⟨96169293286470274869804323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256451448763920732986144861 96169293286470274869804323)
    ·
      refine ⟨144253939929705412304706485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96169293286470274869804323 144253939929705412304706485)
      ·
        refine ⟨13523806868409882403566233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144253939929705412304706485 13523806868409882403566233)
        ·
          refine ⟨10142855151307411802674675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13523806868409882403566233 10142855151307411802674675)
          ·
            refine ⟨15214282726961117704012013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10142855151307411802674675 15214282726961117704012013)
            ·
              refine ⟨5705356022610419139004505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15214282726961117704012013 5705356022610419139004505)
              ·
                refine ⟨4279017016957814354253379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5705356022610419139004505 4279017016957814354253379)
                ·
                  refine ⟨6418525525436721531380069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4279017016957814354253379 6418525525436721531380069)
                  ·
                    refine ⟨1203473536019385287133763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6418525525436721531380069 1203473536019385287133763)
                    ·
                      rfl

theorem cell23_7031269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 1, 4].length) (baseStart_7031269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031269 prefixEnd_7031269 := by exact prefixLift 7031269
  have htrace : WordTrace (prefixWord ++ tailWord_7031269) baseStart_7031269 baseEnd_7031269 := by
    simpa [prefixWord, tailWord_7031269, baseEnd_7031269] using wordTrace_append hprefix tailTrace_7031269
  have hstable : (prefixWord ++ tailWord_7031269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031269).length < 2 ^ (prefixWord ++ tailWord_7031269).sum := by decide
  have hdescent : baseEnd_7031269 < baseStart_7031269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031282 : List Nat := [3, 2, 1, 4, 2, 2, 2, 1, 6]
def baseStart_7031282 : Nat := 118140960795 + 7031282 * 2 ^ 59
def prefixEnd_7031282 : Nat := 4983230072969 + 3 ^ 40 * 7031282 * 2
def baseEnd_7031282 : Nat := 401158587034073812282081

theorem tailTrace_7031282 : CollatzResearch.WordTrace tailWord_7031282 prefixEnd_7031282 401158587034073812282081 := by
  unfold tailWord_7031282
  simp only [CollatzResearch.WordTrace]
  refine ⟨64112980728218409051592025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170967948608582424137578733 64112980728218409051592025)
  ·
    refine ⟨48084735546163806788694019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64112980728218409051592025 48084735546163806788694019)
    ·
      refine ⟨72127103319245710183041029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48084735546163806788694019 72127103319245710183041029)
      ·
        refine ⟨13523831872358570659320193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72127103319245710183041029 13523831872358570659320193)
        ·
          refine ⟨10142873904268927994490145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13523831872358570659320193 10142873904268927994490145)
          ·
            refine ⟨7607155428201695995867609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10142873904268927994490145 7607155428201695995867609)
            ·
              refine ⟨5705366571151271996900707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7607155428201695995867609 5705366571151271996900707)
              ·
                refine ⟨8558049856726907995351061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5705366571151271996900707 8558049856726907995351061)
                ·
                  refine ⟨401158587034073812282081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8558049856726907995351061 401158587034073812282081)
                  ·
                    rfl

theorem cell23_7031282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 6].length) (baseStart_7031282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031282 prefixEnd_7031282 := by exact prefixLift 7031282
  have htrace : WordTrace (prefixWord ++ tailWord_7031282) baseStart_7031282 baseEnd_7031282 := by
    simpa [prefixWord, tailWord_7031282, baseEnd_7031282] using wordTrace_append hprefix tailTrace_7031282
  have hstable : (prefixWord ++ tailWord_7031282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031282).length < 2 ^ (prefixWord ++ tailWord_7031282).sum := by decide
  have hdescent : baseEnd_7031282 < baseStart_7031282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031301 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 3, 1, 5]
def baseStart_7031301 : Nat := 118140960795 + 7031301 * 2 ^ 59
def prefixEnd_7031301 : Nat := 4983230072969 + 3 ^ 40 * 7031301 * 2
def baseEnd_7031301 : Nat := 3610437039439099736201141

theorem tailTrace_7031301 : CollatzResearch.WordTrace tailWord_7031301 prefixEnd_7031301 3610437039439099736201141 := by
  unfold tailWord_7031301
  simp only [CollatzResearch.WordTrace]
  refine ⟨256452615899804802451309757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170968410599869868300873171 256452615899804802451309757)
  ·
    refine ⟨96169730962426800919241159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256452615899804802451309757 96169730962426800919241159)
    ·
      refine ⟨144254596443640201378861739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96169730962426800919241159 144254596443640201378861739)
      ·
        refine ⟨216381894665460302068292609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144254596443640201378861739 216381894665460302068292609)
        ·
          refine ⟨162286420999095226551219457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216381894665460302068292609 162286420999095226551219457)
          ·
            refine ⟨121714815749321419913414593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162286420999095226551219457 121714815749321419913414593)
            ·
              refine ⟨91286111811991064935060945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121714815749321419913414593 91286111811991064935060945)
              ·
                refine ⟨68464583858993298701295709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91286111811991064935060945 68464583858993298701295709)
                ·
                  refine ⟨25674218947122487012985891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68464583858993298701295709 25674218947122487012985891)
                  ·
                    refine ⟨38511328420683730519478837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25674218947122487012985891 38511328420683730519478837)
                    ·
                      refine ⟨3610437039439099736201141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38511328420683730519478837 3610437039439099736201141)
                      ·
                        rfl

theorem cell23_7031301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_7031301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031301 prefixEnd_7031301 := by exact prefixLift 7031301
  have htrace : WordTrace (prefixWord ++ tailWord_7031301) baseStart_7031301 baseEnd_7031301 := by
    simpa [prefixWord, tailWord_7031301, baseEnd_7031301] using wordTrace_append hprefix tailTrace_7031301
  have hstable : (prefixWord ++ tailWord_7031301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031301).length < 2 ^ (prefixWord ++ tailWord_7031301).sum := by decide
  have hdescent : baseEnd_7031301 < baseStart_7031301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031308 : List Nat := [2, 2, 1, 2, 4, 2, 1, 2, 1, 6]
def baseStart_7031308 : Nat := 118140960795 + 7031308 * 2 ^ 59
def prefixEnd_7031308 : Nat := 4983230072969 + 3 ^ 40 * 7031308 * 2
def baseEnd_7031308 : Nat := 1203480211267893736271203

theorem tailTrace_7031308 : CollatzResearch.WordTrace tailWord_7031308 prefixEnd_7031308 1203480211267893736271203 := by
  unfold tailWord_7031308
  simp only [CollatzResearch.WordTrace]
  refine ⟨128226435605389721323407289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170968580807186295097876385 128226435605389721323407289)
  ·
    refine ⟨96169826704042290992555467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128226435605389721323407289 96169826704042290992555467)
    ·
      refine ⟨144254740056063436488833201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96169826704042290992555467 144254740056063436488833201)
      ·
        refine ⟨108191055042047577366624901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144254740056063436488833201 108191055042047577366624901)
        ·
          refine ⟨20285822820383920756242169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108191055042047577366624901 20285822820383920756242169)
          ·
            refine ⟨15214367115287940567181627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20285822820383920756242169 15214367115287940567181627)
            ·
              refine ⟨22821550672931910850772441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15214367115287940567181627 22821550672931910850772441)
              ·
                refine ⟨17116163004698933138079331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22821550672931910850772441 17116163004698933138079331)
                ·
                  refine ⟨25674244507048399707118997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17116163004698933138079331 25674244507048399707118997)
                  ·
                    refine ⟨1203480211267893736271203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25674244507048399707118997 1203480211267893736271203)
                    ·
                      rfl

theorem cell23_7031308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 1, 6].length) (baseStart_7031308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031308 prefixEnd_7031308 := by exact prefixLift 7031308
  have htrace : WordTrace (prefixWord ++ tailWord_7031308) baseStart_7031308 baseEnd_7031308 := by
    simpa [prefixWord, tailWord_7031308, baseEnd_7031308] using wordTrace_append hprefix tailTrace_7031308
  have hstable : (prefixWord ++ tailWord_7031308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031308).length < 2 ^ (prefixWord ++ tailWord_7031308).sum := by decide
  have hdescent : baseEnd_7031308 < baseStart_7031308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031311 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 4]
def baseStart_7031311 : Nat := 118140960795 + 7031311 * 2 ^ 59
def prefixEnd_7031311 : Nat := 4983230072969 + 3 ^ 40 * 7031311 * 2
def baseEnd_7031311 : Nat := 3610442174245644697076095

theorem tailTrace_7031311 : CollatzResearch.WordTrace tailWord_7031311 prefixEnd_7031311 3610442174245644697076095 := by
  unfold tailWord_7031311
  simp only [CollatzResearch.WordTrace]
  refine ⟨256452980629768574159173787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170968653753179049439449191 256452980629768574159173787)
  ·
    refine ⟨384679470944652861238760681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256452980629768574159173787 384679470944652861238760681)
    ·
      refine ⟨288509603208489645929070511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384679470944652861238760681 288509603208489645929070511)
      ·
        refine ⟨432764404812734468893605767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288509603208489645929070511 432764404812734468893605767)
        ·
          refine ⟨649146607219101703340408651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432764404812734468893605767 649146607219101703340408651)
          ·
            refine ⟨973719910828652555010612977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649146607219101703340408651 973719910828652555010612977)
            ·
              refine ⟨730289933121489416257959733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 973719910828652555010612977 730289933121489416257959733)
              ·
                refine ⟨68464681230139632774183725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 730289933121489416257959733 68464681230139632774183725)
                ·
                  refine ⟨25674255461302362290318897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68464681230139632774183725 25674255461302362290318897)
                  ·
                    refine ⟨19255691595976771717739173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25674255461302362290318897 19255691595976771717739173)
                    ·
                      refine ⟨3610442174245644697076095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19255691595976771717739173 3610442174245644697076095)
                      ·
                        rfl

theorem cell23_7031311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 4].length) (baseStart_7031311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031311 prefixEnd_7031311 := by exact prefixLift 7031311
  have htrace : WordTrace (prefixWord ++ tailWord_7031311) baseStart_7031311 baseEnd_7031311 := by
    simpa [prefixWord, tailWord_7031311, baseEnd_7031311] using wordTrace_append hprefix tailTrace_7031311
  have hstable : (prefixWord ++ tailWord_7031311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031311).length < 2 ^ (prefixWord ++ tailWord_7031311).sum := by decide
  have hdescent : baseEnd_7031311 < baseStart_7031311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031315 : List Nat := [1, 1, 1, 2, 1, 5, 5, 1, 1, 1, 4]
def baseStart_7031315 : Nat := 118140960795 + 7031315 * 2 ^ 59
def prefixEnd_7031315 : Nat := 4983230072969 + 3 ^ 40 * 7031315 * 2
def baseEnd_7031315 : Nat := 3610444228168262681426077

theorem tailTrace_7031315 : CollatzResearch.WordTrace tailWord_7031315 prefixEnd_7031315 3610444228168262681426077 := by
  unfold tailWord_7031315
  simp only [CollatzResearch.WordTrace]
  refine ⟨256453126521754082842319399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170968751014502721894879599 256453126521754082842319399)
  ·
    refine ⟨384679689782631124263479099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256453126521754082842319399 384679689782631124263479099)
    ·
      refine ⟨577019534673946686395218649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384679689782631124263479099 577019534673946686395218649)
      ·
        refine ⟨432764651005460014796413987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577019534673946686395218649 432764651005460014796413987)
        ·
          refine ⟨649146976508190022194620981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432764651005460014796413987 649146976508190022194620981)
          ·
            refine ⟨60857529047642814580745717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 649146976508190022194620981 60857529047642814580745717)
            ·
              refine ⟨5705393348216513866944911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60857529047642814580745717 5705393348216513866944911)
              ·
                refine ⟨8558090022324770800417367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5705393348216513866944911 8558090022324770800417367)
                ·
                  refine ⟨12837135033487156200626051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8558090022324770800417367 12837135033487156200626051)
                  ·
                    refine ⟨19255702550230734300939077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12837135033487156200626051 19255702550230734300939077)
                    ·
                      refine ⟨3610444228168262681426077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19255702550230734300939077 3610444228168262681426077)
                      ·
                        rfl

theorem cell23_7031315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 1, 1, 4].length) (baseStart_7031315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031315 prefixEnd_7031315 := by exact prefixLift 7031315
  have htrace : WordTrace (prefixWord ++ tailWord_7031315) baseStart_7031315 baseEnd_7031315 := by
    simpa [prefixWord, tailWord_7031315, baseEnd_7031315] using wordTrace_append hprefix tailTrace_7031315
  have hstable : (prefixWord ++ tailWord_7031315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031315).length < 2 ^ (prefixWord ++ tailWord_7031315).sum := by decide
  have hdescent : baseEnd_7031315 < baseStart_7031315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031325 : List Nat := [1, 4, 2, 2, 1, 2, 1, 4, 2, 4]
def baseStart_7031325 : Nat := 118140960795 + 7031325 * 2 ^ 59
def prefixEnd_7031325 : Nat := 4983230072969 + 3 ^ 40 * 7031325 * 2
def baseEnd_7031325 : Nat := 1203483120991602547433677

theorem tailTrace_7031325 : CollatzResearch.WordTrace tailWord_7031325 prefixEnd_7031325 1203483120991602547433677 := by
  unfold tailWord_7031325
  simp only [CollatzResearch.WordTrace]
  refine ⟨256453491251717854550183429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170968994167811903033455619 256453491251717854550183429)
  ·
    refine ⟨48085029609697097728159393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256453491251717854550183429 48085029609697097728159393)
    ·
      refine ⟨36063772207272823296119545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48085029609697097728159393 36063772207272823296119545)
      ·
        refine ⟨27047829155454617472089659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36063772207272823296119545 27047829155454617472089659)
        ·
          refine ⟨40571743733181926208134489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27047829155454617472089659 40571743733181926208134489)
          ·
            refine ⟨30428807799886444656100867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40571743733181926208134489 30428807799886444656100867)
            ·
              refine ⟨45643211699829666984151301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30428807799886444656100867 45643211699829666984151301)
              ·
                refine ⟨8558102193718062559528369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45643211699829666984151301 8558102193718062559528369)
                ·
                  refine ⟨6418576645288546919646277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8558102193718062559528369 6418576645288546919646277)
                  ·
                    refine ⟨1203483120991602547433677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6418576645288546919646277 1203483120991602547433677)
                    ·
                      rfl

theorem cell23_7031325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_7031325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031325 prefixEnd_7031325 := by exact prefixLift 7031325
  have htrace : WordTrace (prefixWord ++ tailWord_7031325) baseStart_7031325 baseEnd_7031325 := by
    simpa [prefixWord, tailWord_7031325, baseEnd_7031325] using wordTrace_append hprefix tailTrace_7031325
  have hstable : (prefixWord ++ tailWord_7031325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031325).length < 2 ^ (prefixWord ++ tailWord_7031325).sum := by decide
  have hdescent : baseEnd_7031325 < baseStart_7031325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031338 : List Nat := [3, 1, 4, 1, 1, 2, 3, 8]
def baseStart_7031338 : Nat := 118140960795 + 7031338 * 2 ^ 59
def prefixEnd_7031338 : Nat := 4983230072969 + 3 ^ 40 * 7031338 * 2
def baseEnd_7031338 : Nat := 133720594008270966349573

theorem tailTrace_7031338 : CollatzResearch.WordTrace tailWord_7031338 prefixEnd_7031338 133720594008270966349573 := by
  unfold tailWord_7031338
  simp only [CollatzResearch.WordTrace]
  refine ⟨64113491350167689442601667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170969310267113838513604445 64113491350167689442601667)
  ·
    refine ⟨96170237025251534163902501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64113491350167689442601667 96170237025251534163902501)
    ·
      refine ⟨18031919442234662655731719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96170237025251534163902501 18031919442234662655731719)
      ·
        refine ⟨27047879163351993983597579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18031919442234662655731719 27047879163351993983597579)
        ·
          refine ⟨40571818745027990975396369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27047879163351993983597579 40571818745027990975396369)
          ·
            refine ⟨30428864058770993231547277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40571818745027990975396369 30428864058770993231547277)
            ·
              refine ⟨11410824022039122461830229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30428864058770993231547277 11410824022039122461830229)
              ·
                refine ⟨133720594008270966349573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11410824022039122461830229 133720594008270966349573)
                ·
                  rfl

theorem cell23_7031338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 8].length) (baseStart_7031338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031338 prefixEnd_7031338 := by exact prefixLift 7031338
  have htrace : WordTrace (prefixWord ++ tailWord_7031338) baseStart_7031338 baseEnd_7031338 := by
    simpa [prefixWord, tailWord_7031338, baseEnd_7031338] using wordTrace_append hprefix tailTrace_7031338
  have hstable : (prefixWord ++ tailWord_7031338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031338).length < 2 ^ (prefixWord ++ tailWord_7031338).sum := by decide
  have hdescent : baseEnd_7031338 < baseStart_7031338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031351 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 2, 7]
def baseStart_7031351 : Nat := 118140960795 + 7031351 * 2 ^ 59
def prefixEnd_7031351 : Nat := 4983230072969 + 3 ^ 40 * 7031351 * 2
def baseEnd_7031351 : Nat := 1203487571157274846858637

theorem tailTrace_7031351 : CollatzResearch.WordTrace tailWord_7031351 prefixEnd_7031351 1203487571157274846858637 := by
  unfold tailWord_7031351
  simp only [CollatzResearch.WordTrace]
  refine ⟨256454439549623660990629907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170969626366415773993753271 256454439549623660990629907)
  ·
    refine ⟨384681659324435491485944861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256454439549623660990629907 384681659324435491485944861)
    ·
      refine ⟨144255622246663309307229323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384681659324435491485944861 144255622246663309307229323)
      ·
        refine ⟨216383433369994963960843985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144255622246663309307229323 216383433369994963960843985)
        ·
          refine ⟨162287575027496222970632989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216383433369994963960843985 162287575027496222970632989)
          ·
            refine ⟨60857840635311083613987371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162287575027496222970632989 60857840635311083613987371)
            ·
              refine ⟨91286760952966625420981057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60857840635311083613987371 91286760952966625420981057)
              ·
                refine ⟨68465070714724969065735793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91286760952966625420981057 68465070714724969065735793)
                ·
                  refine ⟨51348803036043726799301845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68465070714724969065735793 51348803036043726799301845)
                  ·
                    refine ⟨1203487571157274846858637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51348803036043726799301845 1203487571157274846858637)
                    ·
                      rfl

theorem cell23_7031351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_7031351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031351 prefixEnd_7031351 := by exact prefixLift 7031351
  have htrace : WordTrace (prefixWord ++ tailWord_7031351) baseStart_7031351 baseEnd_7031351 := by
    simpa [prefixWord, tailWord_7031351, baseEnd_7031351] using wordTrace_append hprefix tailTrace_7031351
  have hstable : (prefixWord ++ tailWord_7031351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031351).length < 2 ^ (prefixWord ++ tailWord_7031351).sum := by decide
  have hdescent : baseEnd_7031351 < baseStart_7031351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031366 : List Nat := [6, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4]
def baseStart_7031366 : Nat := 118140960795 + 7031366 * 2 ^ 59
def prefixEnd_7031366 : Nat := 4983230072969 + 3 ^ 40 * 7031366 * 2
def baseEnd_7031366 : Nat := 3610470415681641981888343

theorem tailTrace_7031366 : CollatzResearch.WordTrace tailWord_7031366 prefixEnd_7031366 3610470415681641981888343 := by
  unfold tailWord_7031366
  simp only [CollatzResearch.WordTrace]
  refine ⟨8014218332642791204763311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 170969991096379545701617301 8014218332642791204763311)
  ·
    refine ⟨12021327498964186807144967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8014218332642791204763311 12021327498964186807144967)
    ·
      refine ⟨18031991248446280210717451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12021327498964186807144967 18031991248446280210717451)
      ·
        refine ⟨27047986872669420316076177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18031991248446280210717451 27047986872669420316076177)
        ·
          refine ⟨20285990154502065237057133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27047986872669420316076177 20285990154502065237057133)
          ·
            refine ⟨7607246307938274463896425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20285990154502065237057133 7607246307938274463896425)
            ·
              refine ⟨5705434730953705847922319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7607246307938274463896425 5705434730953705847922319)
              ·
                refine ⟨8558152096430558771883479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5705434730953705847922319 8558152096430558771883479)
                ·
                  refine ⟨12837228144645838157825219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8558152096430558771883479 12837228144645838157825219)
                  ·
                    refine ⟨19255842216968757236737829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12837228144645838157825219 19255842216968757236737829)
                    ·
                      refine ⟨3610470415681641981888343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19255842216968757236737829 3610470415681641981888343)
                      ·
                        rfl

theorem cell23_7031366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_7031366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031366 prefixEnd_7031366 := by exact prefixLift 7031366
  have htrace : WordTrace (prefixWord ++ tailWord_7031366) baseStart_7031366 baseEnd_7031366 := by
    simpa [prefixWord, tailWord_7031366, baseEnd_7031366] using wordTrace_append hprefix tailTrace_7031366
  have hstable : (prefixWord ++ tailWord_7031366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031366).length < 2 ^ (prefixWord ++ tailWord_7031366).sum := by decide
  have hdescent : baseEnd_7031366 < baseStart_7031366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031411 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 9]
def baseStart_7031411 : Nat := 118140960795 + 7031411 * 2 ^ 59
def prefixEnd_7031411 : Nat := 4983230072969 + 3 ^ 40 * 7031411 * 2
def baseEnd_7031411 : Nat := 401165946923454922869515

theorem tailTrace_7031411 : CollatzResearch.WordTrace tailWord_7031411 prefixEnd_7031411 401165946923454922869515 := by
  unfold tailWord_7031411
  simp only [CollatzResearch.WordTrace]
  refine ⟨256456627929406291237814087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170971085286270860825209391 256456627929406291237814087)
  ·
    refine ⟨384684941894109436856721131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256456627929406291237814087 384684941894109436856721131)
    ·
      refine ⟨577027412841164155285081697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384684941894109436856721131 577027412841164155285081697)
      ·
        refine ⟨432770559630873116463811273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577027412841164155285081697 432770559630873116463811273)
        ·
          refine ⟨324577919723154837347858455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 432770559630873116463811273 324577919723154837347858455)
          ·
            refine ⟨486866879584732256021787683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324577919723154837347858455 486866879584732256021787683)
            ·
              refine ⟨730300319377098384032681525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486866879584732256021787683 730300319377098384032681525)
              ·
                refine ⟨68465654941602973503063893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 730300319377098384032681525 68465654941602973503063893)
                ·
                  refine ⟨401165946923454922869515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68465654941602973503063893 401165946923454922869515)
                  ·
                    rfl

theorem cell23_7031411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 9].length) (baseStart_7031411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031411 prefixEnd_7031411 := by exact prefixLift 7031411
  have htrace : WordTrace (prefixWord ++ tailWord_7031411) baseStart_7031411 baseEnd_7031411 := by
    simpa [prefixWord, tailWord_7031411, baseEnd_7031411] using wordTrace_append hprefix tailTrace_7031411
  have hstable : (prefixWord ++ tailWord_7031411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031411).length < 2 ^ (prefixWord ++ tailWord_7031411).sum := by decide
  have hdescent : baseEnd_7031411 < baseStart_7031411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031438 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7]
def baseStart_7031438 : Nat := 118140960795 + 7031438 * 2 ^ 59
def prefixEnd_7031438 : Nat := 4983230072969 + 3 ^ 40 * 7031438 * 2
def baseEnd_7031438 : Nat := 3610507386288765700188011

theorem tailTrace_7031438 : CollatzResearch.WordTrace tailWord_7031438 prefixEnd_7031438 3610507386288765700188011 := by
  unfold tailWord_7031438
  simp only [CollatzResearch.WordTrace]
  refine ⟨32057201587538559356130871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170971741800205649899364645 32057201587538559356130871)
  ·
    refine ⟨48085802381307839034196307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32057201587538559356130871 48085802381307839034196307)
    ·
      refine ⟨72128703571961758551294461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48085802381307839034196307 72128703571961758551294461)
      ·
        refine ⟨27048263839485659456735423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72128703571961758551294461 27048263839485659456735423)
        ·
          refine ⟨40572395759228489185103135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27048263839485659456735423 40572395759228489185103135)
          ·
            refine ⟨60858593638842733777654703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40572395759228489185103135 60858593638842733777654703)
            ·
              refine ⟨91287890458264100666482055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60858593638842733777654703 91287890458264100666482055)
              ·
                refine ⟨136931835687396150999723083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91287890458264100666482055 136931835687396150999723083)
                ·
                  refine ⟨205397753531094226499584625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136931835687396150999723083 205397753531094226499584625)
                  ·
                    refine ⟨154048315148320669874688469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 205397753531094226499584625 154048315148320669874688469)
                    ·
                      refine ⟨3610507386288765700188011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154048315148320669874688469 3610507386288765700188011)
                      ·
                        rfl

theorem cell23_7031438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_7031438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031438 prefixEnd_7031438 := by exact prefixLift 7031438
  have htrace : WordTrace (prefixWord ++ tailWord_7031438) baseStart_7031438 baseEnd_7031438 := by
    simpa [prefixWord, tailWord_7031438, baseEnd_7031438] using wordTrace_append hprefix tailTrace_7031438
  have hstable : (prefixWord ++ tailWord_7031438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031438).length < 2 ^ (prefixWord ++ tailWord_7031438).sum := by decide
  have hdescent : baseEnd_7031438 < baseStart_7031438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031475 : List Nat := [1, 1, 1, 2, 3, 5, 2, 1, 2, 5]
def baseStart_7031475 : Nat := 118140960795 + 7031475 * 2 ^ 59
def prefixEnd_7031475 : Nat := 4983230072969 + 3 ^ 40 * 7031475 * 2
def baseEnd_7031475 : Nat := 1203508795024327351808447

theorem tailTrace_7031475 : CollatzResearch.WordTrace tailWord_7031475 prefixEnd_7031475 1203508795024327351808447 := by
  unfold tailWord_7031475
  simp only [CollatzResearch.WordTrace]
  refine ⟨256458962201174430168143879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170972641467449620112095919 256458962201174430168143879)
  ·
    refine ⟨384688443301761645252215819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256458962201174430168143879 384688443301761645252215819)
    ·
      refine ⟨577032664952642467878323729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384688443301761645252215819 577032664952642467878323729)
      ·
        refine ⟨432774498714481850908742797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577032664952642467878323729 432774498714481850908742797)
        ·
          refine ⟨162290437017930694090778549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 432774498714481850908742797 162290437017930694090778549)
          ·
            refine ⟨15214728470431002571010489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162290437017930694090778549 15214728470431002571010489)
            ·
              refine ⟨11411046352823251928257867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15214728470431002571010489 11411046352823251928257867)
              ·
                refine ⟨17116569529234877892386801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11411046352823251928257867 17116569529234877892386801)
                ·
                  refine ⟨12837427146926158419290101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17116569529234877892386801 12837427146926158419290101)
                  ·
                    refine ⟨1203508795024327351808447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12837427146926158419290101 1203508795024327351808447)
                    ·
                      rfl

theorem cell23_7031475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 5].length) (baseStart_7031475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031475 prefixEnd_7031475 := by exact prefixLift 7031475
  have htrace : WordTrace (prefixWord ++ tailWord_7031475) baseStart_7031475 baseEnd_7031475 := by
    simpa [prefixWord, tailWord_7031475, baseEnd_7031475] using wordTrace_append hprefix tailTrace_7031475
  have hstable : (prefixWord ++ tailWord_7031475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031475).length < 2 ^ (prefixWord ++ tailWord_7031475).sum := by decide
  have hdescent : baseEnd_7031475 < baseStart_7031475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031505 : List Nat := [1, 2, 2, 1, 2, 3, 2, 3, 3, 4]
def baseStart_7031505 : Nat := 118140960795 + 7031505 * 2 ^ 59
def prefixEnd_7031505 : Nat := 4983230072969 + 3 ^ 40 * 7031505 * 2
def baseEnd_7031505 : Nat := 1203513929830872312683401

theorem tailTrace_7031505 : CollatzResearch.WordTrace tailWord_7031505 prefixEnd_7031505 1203513929830872312683401 := by
  unfold tailWord_7031505
  simp only [CollatzResearch.WordTrace]
  refine ⟨256460056391065745291735969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170973370927377163527823979 256460056391065745291735969)
  ·
    refine ⟨192345042293299308968801977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256460056391065745291735969 192345042293299308968801977)
    ·
      refine ⟨144258781719974481726601483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192345042293299308968801977 144258781719974481726601483)
      ·
        refine ⟨216388172579961722589902225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144258781719974481726601483 216388172579961722589902225)
        ·
          refine ⟨162291129434971291942426669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216388172579961722589902225 162291129434971291942426669)
          ·
            refine ⟨60859173538114234478410001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162291129434971291942426669 60859173538114234478410001)
            ·
              refine ⟨45644380153585675858807501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60859173538114234478410001 45644380153585675858807501)
              ·
                refine ⟨17116642557594628447052813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45644380153585675858807501 17116642557594628447052813)
                ·
                  refine ⟨6418740959097985667644805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17116642557594628447052813 6418740959097985667644805)
                  ·
                    refine ⟨1203513929830872312683401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6418740959097985667644805 1203513929830872312683401)
                    ·
                      rfl

theorem cell23_7031505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 4].length) (baseStart_7031505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031505 prefixEnd_7031505 := by exact prefixLift 7031505
  have htrace : WordTrace (prefixWord ++ tailWord_7031505) baseStart_7031505 baseEnd_7031505 := by
    simpa [prefixWord, tailWord_7031505, baseEnd_7031505] using wordTrace_append hprefix tailTrace_7031505
  have hstable : (prefixWord ++ tailWord_7031505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031505).length < 2 ^ (prefixWord ++ tailWord_7031505).sum := by decide
  have hdescent : baseEnd_7031505 < baseStart_7031505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031512 : List Nat := [2, 1, 2, 2, 3, 3, 1, 1, 2, 4, 2]
def baseStart_7031512 : Nat := 118140960795 + 7031512 * 2 ^ 59
def prefixEnd_7031512 : Nat := 4983230072969 + 3 ^ 40 * 7031512 * 2
def baseEnd_7031512 : Nat := 3610545383857198410662671

theorem tailTrace_7031512 : CollatzResearch.WordTrace tailWord_7031512 prefixEnd_7031512 3610545383857198410662671 := by
  unfold tailWord_7031512
  simp only [CollatzResearch.WordTrace]
  refine ⟨128230155851020192743620395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170973541134693590324827193 128230155851020192743620395)
  ·
    refine ⟨192345233776530289115430593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128230155851020192743620395 192345233776530289115430593)
    ·
      refine ⟨144258925332397716836572945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192345233776530289115430593 144258925332397716836572945)
      ·
        refine ⟨108194193999298287627429709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144258925332397716836572945 108194193999298287627429709)
        ·
          refine ⟨40572822749736857860286141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108194193999298287627429709 40572822749736857860286141)
          ·
            refine ⟨15214808531151321697607303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40572822749736857860286141 15214808531151321697607303)
            ·
              refine ⟨22822212796726982546410955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15214808531151321697607303 22822212796726982546410955)
              ·
                refine ⟨34233319195090473819616433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22822212796726982546410955 34233319195090473819616433)
                ·
                  refine ⟨25674989396317855364712325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34233319195090473819616433 25674989396317855364712325)
                  ·
                    refine ⟨4814060511809597880883561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25674989396317855364712325 4814060511809597880883561)
                    ·
                      refine ⟨3610545383857198410662671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4814060511809597880883561 3610545383857198410662671)
                      ·
                        rfl

theorem cell23_7031512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 2, 4, 2].length) (baseStart_7031512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031512 prefixEnd_7031512 := by exact prefixLift 7031512
  have htrace : WordTrace (prefixWord ++ tailWord_7031512) baseStart_7031512 baseEnd_7031512 := by
    simpa [prefixWord, tailWord_7031512, baseEnd_7031512] using wordTrace_append hprefix tailTrace_7031512
  have hstable : (prefixWord ++ tailWord_7031512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031512).length < 2 ^ (prefixWord ++ tailWord_7031512).sum := by decide
  have hdescent : baseEnd_7031512 < baseStart_7031512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031595 : List Nat := [1, 1, 1, 1, 2, 1, 2, 6, 4, 4]
def baseStart_7031595 : Nat := 118140960795 + 7031595 * 2 ^ 59
def prefixEnd_7031595 : Nat := 4983230072969 + 3 ^ 40 * 7031595 * 2
def baseEnd_7031595 : Nat := 1203529334250507195308263

theorem tailTrace_7031595 : CollatzResearch.WordTrace tailWord_7031595 prefixEnd_7031595 1203529334250507195308263 := by
  unfold tailWord_7031595
  simp only [CollatzResearch.WordTrace]
  refine ⟨256463338960739690662512239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170975559307159793775008159 256463338960739690662512239)
  ·
    refine ⟨384695008441109535993768359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256463338960739690662512239 384695008441109535993768359)
    ·
      refine ⟨577042512661664303990652539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384695008441109535993768359 577042512661664303990652539)
      ·
        refine ⟨865563768992496455985978809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577042512661664303990652539 865563768992496455985978809)
        ·
          refine ⟨649172826744372341989484107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 865563768992496455985978809 649172826744372341989484107)
          ·
            refine ⟨973759240116558512984226161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649172826744372341989484107 973759240116558512984226161)
            ·
              refine ⟨730319430087418884738169621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 973759240116558512984226161 730319430087418884738169621)
              ·
                refine ⟨34233723285347760222101701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 730319430087418884738169621 34233723285347760222101701)
                ·
                  refine ⟨6418823116002705041644069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34233723285347760222101701 6418823116002705041644069)
                  ·
                    refine ⟨1203529334250507195308263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6418823116002705041644069 1203529334250507195308263)
                    ·
                      rfl

theorem cell23_7031595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 4].length) (baseStart_7031595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031595 prefixEnd_7031595 := by exact prefixLift 7031595
  have htrace : WordTrace (prefixWord ++ tailWord_7031595) baseStart_7031595 baseEnd_7031595 := by
    simpa [prefixWord, tailWord_7031595, baseEnd_7031595] using wordTrace_append hprefix tailTrace_7031595
  have hstable : (prefixWord ++ tailWord_7031595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031595).length < 2 ^ (prefixWord ++ tailWord_7031595).sum := by decide
  have hdescent : baseEnd_7031595 < baseStart_7031595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031602 : List Nat := [3, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4]
def baseStart_7031602 : Nat := 118140960795 + 7031602 * 2 ^ 59
def prefixEnd_7031602 : Nat := 4983230072969 + 3 ^ 40 * 7031602 * 2
def baseEnd_7031602 : Nat := 3610591597116103058537257

theorem tailTrace_7031602 : CollatzResearch.WordTrace tailWord_7031602 prefixEnd_7031602 3610591597116103058537257 := by
  unfold tailWord_7031602
  simp only [CollatzResearch.WordTrace]
  refine ⟨64115898567928582714504265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170975729514476220572011373 64115898567928582714504265)
  ·
    refine ⟨48086923925946437035878199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64115898567928582714504265 48086923925946437035878199)
    ·
      refine ⟨72130385888919655553817299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48086923925946437035878199 72130385888919655553817299)
      ·
        refine ⟨108195578833379483330725949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72130385888919655553817299 108195578833379483330725949)
        ·
          refine ⟨40573342062517306249022231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108195578833379483330725949 40573342062517306249022231)
          ·
            refine ⟨60860013093775959373533347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40573342062517306249022231 60860013093775959373533347)
            ·
              refine ⟨91290019640663939060300021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60860013093775959373533347 91290019640663939060300021)
              ·
                refine ⟨8558439341312244286903127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91290019640663939060300021 8558439341312244286903127)
                ·
                  refine ⟨12837659011968366430354691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8558439341312244286903127 12837659011968366430354691)
                  ·
                    refine ⟨19256488517952549645532037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12837659011968366430354691 19256488517952549645532037)
                    ·
                      refine ⟨3610591597116103058537257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19256488517952549645532037 3610591597116103058537257)
                      ·
                        rfl

theorem cell23_7031602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_7031602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031602 prefixEnd_7031602 := by exact prefixLift 7031602
  have htrace : WordTrace (prefixWord ++ tailWord_7031602) baseStart_7031602 baseEnd_7031602 := by
    simpa [prefixWord, tailWord_7031602, baseEnd_7031602] using wordTrace_append hprefix tailTrace_7031602
  have hstable : (prefixWord ++ tailWord_7031602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031602).length < 2 ^ (prefixWord ++ tailWord_7031602).sum := by decide
  have hdescent : baseEnd_7031602 < baseStart_7031602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031612 : List Nat := [2, 2, 2, 2, 1, 1, 1, 6, 2, 4]
def baseStart_7031612 : Nat := 118140960795 + 7031612 * 2 ^ 59
def prefixEnd_7031612 : Nat := 4983230072969 + 3 ^ 40 * 7031612 * 2
def baseEnd_7031612 : Nat := 1203532243974216006470737

theorem tailTrace_7031612 : CollatzResearch.WordTrace tailWord_7031612 prefixEnd_7031612 1203532243974216006470737 := by
  unfold tailWord_7031612
  simp only [CollatzResearch.WordTrace]
  refine ⟨128231979500839051282940545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170975972667785401710587393 128231979500839051282940545)
  ·
    refine ⟨96173984625629288462205409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128231979500839051282940545 96173984625629288462205409)
    ·
      refine ⟨72130488469221966346654057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96173984625629288462205409 72130488469221966346654057)
      ·
        refine ⟨54097866351916474759990543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72130488469221966346654057 54097866351916474759990543)
        ·
          refine ⟨81146799527874712139985815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54097866351916474759990543 81146799527874712139985815)
          ·
            refine ⟨121720199291812068209978723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81146799527874712139985815 121720199291812068209978723)
            ·
              refine ⟨182580298937718102314968085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121720199291812068209978723 182580298937718102314968085)
              ·
                refine ⟨8558451512705536046014129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 182580298937718102314968085 8558451512705536046014129)
                ·
                  refine ⟨6418838634529152034510597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8558451512705536046014129 6418838634529152034510597)
                  ·
                    refine ⟨1203532243974216006470737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6418838634529152034510597 1203532243974216006470737)
                    ·
                      rfl

theorem cell23_7031612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_7031612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031612 prefixEnd_7031612 := by exact prefixLift 7031612
  have htrace : WordTrace (prefixWord ++ tailWord_7031612) baseStart_7031612 baseEnd_7031612 := by
    simpa [prefixWord, tailWord_7031612, baseEnd_7031612] using wordTrace_append hprefix tailTrace_7031612
  have hstable : (prefixWord ++ tailWord_7031612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031612).length < 2 ^ (prefixWord ++ tailWord_7031612).sum := by decide
  have hdescent : baseEnd_7031612 < baseStart_7031612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031613 : List Nat := [1, 4, 1, 4, 3, 1, 1, 1, 3, 1, 3]
def baseStart_7031613 : Nat := 118140960795 + 7031613 * 2 ^ 59
def prefixEnd_7031613 : Nat := 4983230072969 + 3 ^ 40 * 7031613 * 2
def baseEnd_7031613 : Nat := 3610597245403302515499707

theorem tailTrace_7031613 : CollatzResearch.WordTrace tailWord_7031613 prefixEnd_7031613 3610597245403302515499707 := by
  unfold tailWord_7031613
  simp only [CollatzResearch.WordTrace]
  refine ⟨256463995474674479736667493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170975996983116319824444995 256463995474674479736667493)
  ·
    refine ⟨48086999151501464950625155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256463995474674479736667493 48086999151501464950625155)
    ·
      refine ⟨72130498727252197425937733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48086999151501464950625155 72130498727252197425937733)
      ·
        refine ⟨13524468511359787017363325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72130498727252197425937733 13524468511359787017363325)
        ·
          refine ⟨5071675691759920131511247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13524468511359787017363325 5071675691759920131511247)
          ·
            refine ⟨7607513537639880197266871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5071675691759920131511247 7607513537639880197266871)
            ·
              refine ⟨11411270306459820295900307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7607513537639880197266871 11411270306459820295900307)
              ·
                refine ⟨17116905459689730443850461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11411270306459820295900307 17116905459689730443850461)
                ·
                  refine ⟨6418839547383648916443923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17116905459689730443850461 6418839547383648916443923)
                  ·
                    refine ⟨9628259321075473374665885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6418839547383648916443923 9628259321075473374665885)
                    ·
                      refine ⟨3610597245403302515499707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9628259321075473374665885 3610597245403302515499707)
                      ·
                        rfl

theorem cell23_7031613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_7031613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031613 prefixEnd_7031613 := by exact prefixLift 7031613
  have htrace : WordTrace (prefixWord ++ tailWord_7031613) baseStart_7031613 baseEnd_7031613 := by
    simpa [prefixWord, tailWord_7031613, baseEnd_7031613] using wordTrace_append hprefix tailTrace_7031613
  have hstable : (prefixWord ++ tailWord_7031613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031613).length < 2 ^ (prefixWord ++ tailWord_7031613).sum := by decide
  have hdescent : baseEnd_7031613 < baseStart_7031613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031615 : List Nat := [1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 6]
def baseStart_7031615 : Nat := 118140960795 + 7031615 * 2 ^ 59
def prefixEnd_7031615 : Nat := 4983230072969 + 3 ^ 40 * 7031615 * 2
def baseEnd_7031615 : Nat := 3610598272364611507674697

theorem tailTrace_7031615 : CollatzResearch.WordTrace tailWord_7031615 prefixEnd_7031615 3610598272364611507674697 := by
  unfold tailWord_7031615
  simp only [CollatzResearch.WordTrace]
  refine ⟨256464068420667234078240299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170976045613778156052160199 256464068420667234078240299)
  ·
    refine ⟨384696102631000851117360449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256464068420667234078240299 384696102631000851117360449)
    ·
      refine ⟨288522076973250638338020337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384696102631000851117360449 288522076973250638338020337)
      ·
        refine ⟨216391557729937978753515253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288522076973250638338020337 216391557729937978753515253)
        ·
          refine ⟨20286708537181685508142055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 216391557729937978753515253 20286708537181685508142055)
          ·
            refine ⟨30430062805772528262213083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20286708537181685508142055 30430062805772528262213083)
            ·
              refine ⟨45645094208658792393319625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30430062805772528262213083 45645094208658792393319625)
              ·
                refine ⟨34233820656494094294989719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45645094208658792393319625 34233820656494094294989719)
                ·
                  refine ⟨51350730984741141442484579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34233820656494094294989719 51350730984741141442484579)
                  ·
                    refine ⟨77026096477111712163726869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51350730984741141442484579 77026096477111712163726869)
                    ·
                      refine ⟨3610598272364611507674697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77026096477111712163726869 3610598272364611507674697)
                      ·
                        rfl

theorem cell23_7031615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_7031615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031615 prefixEnd_7031615 := by exact prefixLift 7031615
  have htrace : WordTrace (prefixWord ++ tailWord_7031615) baseStart_7031615 baseEnd_7031615 := by
    simpa [prefixWord, tailWord_7031615, baseEnd_7031615] using wordTrace_append hprefix tailTrace_7031615
  have hstable : (prefixWord ++ tailWord_7031615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031615).length < 2 ^ (prefixWord ++ tailWord_7031615).sum := by decide
  have hdescent : baseEnd_7031615 < baseStart_7031615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031625 : List Nat := [1, 2, 1, 1, 2, 6, 2, 8]
def baseStart_7031625 : Nat := 118140960795 + 7031625 * 2 ^ 59
def prefixEnd_7031625 : Nat := 4983230072969 + 3 ^ 40 * 7031625 * 2
def baseEnd_7031625 : Nat := 133726052117450239575913

theorem tailTrace_7031625 : CollatzResearch.WordTrace tailWord_7031625 prefixEnd_7031625 133726052117450239575913 := by
  unfold tailWord_7031625
  simp only [CollatzResearch.WordTrace]
  refine ⟨256464433150631005786104329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170976288767087337190736219 256464433150631005786104329)
  ·
    refine ⟨192348324862973254339578247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256464433150631005786104329 192348324862973254339578247)
    ·
      refine ⟨288522487294459881509367371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192348324862973254339578247 288522487294459881509367371)
      ·
        refine ⟨432783730941689822264051057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288522487294459881509367371 432783730941689822264051057)
        ·
          refine ⟨324587798206267366698038293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 432783730941689822264051057 324587798206267366698038293)
          ·
            refine ⟨15215053040918782813970545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 324587798206267366698038293 15215053040918782813970545)
            ·
              refine ⟨11411289780689087110477909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15215053040918782813970545 11411289780689087110477909)
              ·
                refine ⟨133726052117450239575913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11411289780689087110477909 133726052117450239575913)
                ·
                  rfl

theorem cell23_7031625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 8].length) (baseStart_7031625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031625 prefixEnd_7031625 := by exact prefixLift 7031625
  have htrace : WordTrace (prefixWord ++ tailWord_7031625) baseStart_7031625 baseEnd_7031625 := by
    simpa [prefixWord, tailWord_7031625, baseEnd_7031625] using wordTrace_append hprefix tailTrace_7031625
  have hstable : (prefixWord ++ tailWord_7031625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031625).length < 2 ^ (prefixWord ++ tailWord_7031625).sum := by decide
  have hdescent : baseEnd_7031625 < baseStart_7031625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031635 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 3]
def baseStart_7031635 : Nat := 118140960795 + 7031635 * 2 ^ 59
def prefixEnd_7031635 : Nat := 4983230072969 + 3 ^ 40 * 7031635 * 2
def baseEnd_7031635 : Nat := 3610608541977701429424605

theorem tailTrace_7031635 : CollatzResearch.WordTrace tailWord_7031635 prefixEnd_7031635 3610608541977701429424605 := by
  unfold tailWord_7031635
  simp only [CollatzResearch.WordTrace]
  refine ⟨256464797880594777493968359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170976531920396518329312239 256464797880594777493968359)
  ·
    refine ⟨384697196820892166240952539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256464797880594777493968359 384697196820892166240952539)
    ·
      refine ⟨577045795231338249361428809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384697196820892166240952539 577045795231338249361428809)
      ·
        refine ⟨432784346423503687021071607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577045795231338249361428809 432784346423503687021071607)
        ·
          refine ⟨649176519635255530531607411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432784346423503687021071607 649176519635255530531607411)
          ·
            refine ⟨973764779452883295797411117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649176519635255530531607411 973764779452883295797411117)
            ·
              refine ⟨365161792294831235924029169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 973764779452883295797411117 365161792294831235924029169)
              ·
                refine ⟨273871344221123426943021877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 365161792294831235924029169 273871344221123426943021877)
                ·
                  refine ⟨25675438520730321275908301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 273871344221123426943021877 25675438520730321275908301)
                  ·
                    refine ⟨9628289445273870478465613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25675438520730321275908301 9628289445273870478465613)
                    ·
                      refine ⟨3610608541977701429424605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9628289445273870478465613 3610608541977701429424605)
                      ·
                        rfl

theorem cell23_7031635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 3].length) (baseStart_7031635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031635 prefixEnd_7031635 := by exact prefixLift 7031635
  have htrace : WordTrace (prefixWord ++ tailWord_7031635) baseStart_7031635 baseEnd_7031635 := by
    simpa [prefixWord, tailWord_7031635, baseEnd_7031635] using wordTrace_append hprefix tailTrace_7031635
  have hstable : (prefixWord ++ tailWord_7031635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031635).length < 2 ^ (prefixWord ++ tailWord_7031635).sum := by decide
  have hdescent : baseEnd_7031635 < baseStart_7031635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031636 : List Nat := [2, 4, 1, 1, 4, 2, 1, 2, 1, 1, 4]
def baseStart_7031636 : Nat := 118140960795 + 7031636 * 2 ^ 59
def prefixEnd_7031636 : Nat := 4983230072969 + 3 ^ 40 * 7031636 * 2
def baseEnd_7031636 : Nat := 3610609055458355925512101

theorem tailTrace_7031636 : CollatzResearch.WordTrace tailWord_7031636 prefixEnd_7031636 3610609055458355925512101 := by
  unfold tailWord_7031636
  simp only [CollatzResearch.WordTrace]
  refine ⟨128232417176795577332377381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170976556235727436443169841 128232417176795577332377381)
  ·
    refine ⟨24043578220649170749820759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128232417176795577332377381 24043578220649170749820759)
    ·
      refine ⟨36065367330973756124731139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24043578220649170749820759 36065367330973756124731139)
      ·
        refine ⟨54098050996460634187096709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36065367330973756124731139 54098050996460634187096709)
        ·
          refine ⟨10143384561836368910080633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54098050996460634187096709 10143384561836368910080633)
          ·
            refine ⟨7607538421377276682560475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10143384561836368910080633 7607538421377276682560475)
            ·
              refine ⟨11411307632065915023840713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7607538421377276682560475 11411307632065915023840713)
              ·
                refine ⟨8558480724049436267880535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11411307632065915023840713 8558480724049436267880535)
                ·
                  refine ⟨12837721086074154401820803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8558480724049436267880535 12837721086074154401820803)
                  ·
                    refine ⟨19256581629111231602731205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12837721086074154401820803 19256581629111231602731205)
                    ·
                      refine ⟨3610609055458355925512101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19256581629111231602731205 3610609055458355925512101)
                      ·
                        rfl

theorem cell23_7031636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_7031636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031636 prefixEnd_7031636 := by exact prefixLift 7031636
  have htrace : WordTrace (prefixWord ++ tailWord_7031636) baseStart_7031636 baseEnd_7031636 := by
    simpa [prefixWord, tailWord_7031636, baseEnd_7031636] using wordTrace_append hprefix tailTrace_7031636
  have hstable : (prefixWord ++ tailWord_7031636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031636).length < 2 ^ (prefixWord ++ tailWord_7031636).sum := by decide
  have hdescent : baseEnd_7031636 < baseStart_7031636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031639 : List Nat := [1, 1, 3, 2, 4, 1, 3, 2, 1, 2, 3]
def baseStart_7031639 : Nat := 118140960795 + 7031639 * 2 ^ 59
def prefixEnd_7031639 : Nat := 4983230072969 + 3 ^ 40 * 7031639 * 2
def baseEnd_7031639 : Nat := 3610610595900319413774587

theorem tailTrace_7031639 : CollatzResearch.WordTrace tailWord_7031639 prefixEnd_7031639 3610610595900319413774587 := by
  unfold tailWord_7031639
  simp only [CollatzResearch.WordTrace]
  refine ⟨256464943772580286177113971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170976629181720190784742647 256464943772580286177113971)
  ·
    refine ⟨384697415658870429265670957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256464943772580286177113971 384697415658870429265670957)
    ·
      refine ⟨144261530872076410974626609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384697415658870429265670957 144261530872076410974626609)
      ·
        refine ⟨108196148154057308230969957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144261530872076410974626609 108196148154057308230969957)
        ·
          refine ⟨20286777778885745293306867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108196148154057308230969957 20286777778885745293306867)
          ·
            refine ⟨30430166668328617939960301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20286777778885745293306867 30430166668328617939960301)
            ·
              refine ⟨11411312500623231727485113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30430166668328617939960301 11411312500623231727485113)
              ·
                refine ⟨8558484375467423795613835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11411312500623231727485113 8558484375467423795613835)
                ·
                  refine ⟨12837726563201135693420753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8558484375467423795613835 12837726563201135693420753)
                  ·
                    refine ⟨9628294922400851770065565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12837726563201135693420753 9628294922400851770065565)
                    ·
                      refine ⟨3610610595900319413774587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9628294922400851770065565 3610610595900319413774587)
                      ·
                        rfl

theorem cell23_7031639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_7031639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031639 prefixEnd_7031639 := by exact prefixLift 7031639
  have htrace : WordTrace (prefixWord ++ tailWord_7031639) baseStart_7031639 baseEnd_7031639 := by
    simpa [prefixWord, tailWord_7031639, baseEnd_7031639] using wordTrace_append hprefix tailTrace_7031639
  have hstable : (prefixWord ++ tailWord_7031639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031639).length < 2 ^ (prefixWord ++ tailWord_7031639).sum := by decide
  have hdescent : baseEnd_7031639 < baseStart_7031639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031652 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 3, 3, 3]
def baseStart_7031652 : Nat := 118140960795 + 7031652 * 2 ^ 59
def prefixEnd_7031652 : Nat := 4983230072969 + 3 ^ 40 * 7031652 * 2
def baseEnd_7031652 : Nat := 3610617271148827862912027

theorem tailTrace_7031652 : CollatzResearch.WordTrace tailWord_7031652 prefixEnd_7031652 3610617271148827862912027 := by
  unfold tailWord_7031652
  simp only [CollatzResearch.WordTrace]
  refine ⟨128232708960766594698668605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170976945281022126264891473 128232708960766594698668605)
  ·
    refine ⟨48087265860287473012000727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128232708960766594698668605 48087265860287473012000727)
    ·
      refine ⟨72130898790431209518001091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48087265860287473012000727 72130898790431209518001091)
      ·
        refine ⟨108196348185646814277001637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72130898790431209518001091 108196348185646814277001637)
        ·
          refine ⟨20286815284808777676937807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108196348185646814277001637 20286815284808777676937807)
          ·
            refine ⟨30430222927213166515406711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20286815284808777676937807 30430222927213166515406711)
            ·
              refine ⟨45645334390819749773110067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30430222927213166515406711 45645334390819749773110067)
              ·
                refine ⟨68468001586229624659665101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45645334390819749773110067 68468001586229624659665101)
                ·
                  refine ⟨25675500594836109247374413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68468001586229624659665101 25675500594836109247374413)
                  ·
                    refine ⟨9628312723063540967765405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25675500594836109247374413 9628312723063540967765405)
                    ·
                      refine ⟨3610617271148827862912027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9628312723063540967765405 3610617271148827862912027)
                      ·
                        rfl

theorem cell23_7031652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_7031652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031652 prefixEnd_7031652 := by exact prefixLift 7031652
  have htrace : WordTrace (prefixWord ++ tailWord_7031652) baseStart_7031652 baseEnd_7031652 := by
    simpa [prefixWord, tailWord_7031652, baseEnd_7031652] using wordTrace_append hprefix tailTrace_7031652
  have hstable : (prefixWord ++ tailWord_7031652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031652).length < 2 ^ (prefixWord ++ tailWord_7031652).sum := by decide
  have hdescent : baseEnd_7031652 < baseStart_7031652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031656 : List Nat := [2, 1, 4, 2, 1, 3, 3, 1, 1, 2, 3]
def baseStart_7031656 : Nat := 118140960795 + 7031656 * 2 ^ 59
def prefixEnd_7031656 : Nat := 4983230072969 + 3 ^ 40 * 7031656 * 2
def baseEnd_7031656 : Nat := 3610619325071445847262009

theorem tailTrace_7031656 : CollatzResearch.WordTrace tailWord_7031656 prefixEnd_7031656 3610619325071445847262009 := by
  unfold tailWord_7031656
  simp only [CollatzResearch.WordTrace]
  refine ⟨128232781906759349040241411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170977042542345798720321881 128232781906759349040241411)
  ·
    refine ⟨192349172860139023560362117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128232781906759349040241411 192349172860139023560362117)
    ·
      refine ⟨36065469911276066917567897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192349172860139023560362117 36065469911276066917567897)
      ·
        refine ⟨27049102433457050188175923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36065469911276066917567897 27049102433457050188175923)
        ·
          refine ⟨40573653650185575282263885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27049102433457050188175923 40573653650185575282263885)
          ·
            refine ⟨15215120118819590730848957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40573653650185575282263885 15215120118819590730848957)
            ·
              refine ⟨5705670044557346524068359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15215120118819590730848957 5705670044557346524068359)
              ·
                refine ⟨8558505066836019786102539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5705670044557346524068359 8558505066836019786102539)
                ·
                  refine ⟨12837757600254029679153809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8558505066836019786102539 12837757600254029679153809)
                  ·
                    refine ⟨9628318200190522259365357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12837757600254029679153809 9628318200190522259365357)
                    ·
                      refine ⟨3610619325071445847262009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9628318200190522259365357 3610619325071445847262009)
                      ·
                        rfl

theorem cell23_7031656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_7031656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031656 prefixEnd_7031656 := by exact prefixLift 7031656
  have htrace : WordTrace (prefixWord ++ tailWord_7031656) baseStart_7031656 baseEnd_7031656 := by
    simpa [prefixWord, tailWord_7031656, baseEnd_7031656] using wordTrace_append hprefix tailTrace_7031656
  have hstable : (prefixWord ++ tailWord_7031656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031656).length < 2 ^ (prefixWord ++ tailWord_7031656).sum := by decide
  have hdescent : baseEnd_7031656 < baseStart_7031656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031670 : List Nat := [5, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2]
def baseStart_7031670 : Nat := 118140960795 + 7031670 * 2 ^ 59
def prefixEnd_7031670 : Nat := 4983230072969 + 3 ^ 40 * 7031670 * 2
def baseEnd_7031670 : Nat := 3610626513800608792486945

theorem tailTrace_7031670 : CollatzResearch.WordTrace tailWord_7031670 prefixEnd_7031670 3610626513800608792486945 := by
  unfold tailWord_7031670
  simp only [CollatzResearch.WordTrace]
  refine ⟨16029129652216748654468279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170977382956978652314328309 16029129652216748654468279)
  ·
    refine ⟨24043694478325122981702419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16029129652216748654468279 24043694478325122981702419)
    ·
      refine ⟨36065541717487684472553629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24043694478325122981702419 36065541717487684472553629)
      ·
        refine ⟨13524578144057881677207611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36065541717487684472553629 13524578144057881677207611)
        ·
          refine ⟨20286867216086822515811417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13524578144057881677207611 20286867216086822515811417)
          ·
            refine ⟨15215150412065116886858563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20286867216086822515811417 15215150412065116886858563)
            ·
              refine ⟨22822725618097675330287845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15215150412065116886858563 22822725618097675330287845)
              ·
                refine ⟨4279261053393314124428971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22822725618097675330287845 4279261053393314124428971)
                ·
                  refine ⟨6418891580089971186643457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4279261053393314124428971 6418891580089971186643457)
                  ·
                    refine ⟨4814168685067478389982593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6418891580089971186643457 4814168685067478389982593)
                    ·
                      refine ⟨3610626513800608792486945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4814168685067478389982593 3610626513800608792486945)
                      ·
                        rfl

theorem cell23_7031670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_7031670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031670 prefixEnd_7031670 := by exact prefixLift 7031670
  have htrace : WordTrace (prefixWord ++ tailWord_7031670) baseStart_7031670 baseEnd_7031670 := by
    simpa [prefixWord, tailWord_7031670, baseEnd_7031670] using wordTrace_append hprefix tailTrace_7031670
  have hstable : (prefixWord ++ tailWord_7031670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031670).length < 2 ^ (prefixWord ++ tailWord_7031670).sum := by decide
  have hdescent : baseEnd_7031670 < baseStart_7031670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031675 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 4]
def baseStart_7031675 : Nat := 118140960795 + 7031675 * 2 ^ 59
def prefixEnd_7031675 : Nat := 4983230072969 + 3 ^ 40 * 7031675 * 2
def baseEnd_7031675 : Nat := 3610629081203881272924421

theorem tailTrace_7031675 : CollatzResearch.WordTrace tailWord_7031675 prefixEnd_7031675 3610629081203881272924421 := by
  unfold tailWord_7031675
  simp only [CollatzResearch.WordTrace]
  refine ⟨256466256800449864325424479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170977504533633242883616319 256466256800449864325424479)
  ·
    refine ⟨384699385200674796488136719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256466256800449864325424479 384699385200674796488136719)
    ·
      refine ⟨577049077801012194732205079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384699385200674796488136719 577049077801012194732205079)
      ·
        refine ⟨865573616701518292098307619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577049077801012194732205079 865573616701518292098307619)
        ·
          refine ⟨1298360425052277438147461429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 865573616701518292098307619 1298360425052277438147461429)
          ·
            refine ⟨121721289848651009826324509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1298360425052277438147461429 121721289848651009826324509)
            ·
              refine ⟨45645483693244128684871691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121721289848651009826324509 45645483693244128684871691)
              ·
                refine ⟨68468225539866193027307537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45645483693244128684871691 68468225539866193027307537)
                ·
                  refine ⟨51351169154899644770480653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68468225539866193027307537 51351169154899644770480653)
                  ·
                    refine ⟨19256688433087366788930245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51351169154899644770480653 19256688433087366788930245)
                    ·
                      refine ⟨3610629081203881272924421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19256688433087366788930245 3610629081203881272924421)
                      ·
                        rfl

theorem cell23_7031675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 4].length) (baseStart_7031675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031675 prefixEnd_7031675 := by exact prefixLift 7031675
  have htrace : WordTrace (prefixWord ++ tailWord_7031675) baseStart_7031675 baseEnd_7031675 := by
    simpa [prefixWord, tailWord_7031675, baseEnd_7031675] using wordTrace_append hprefix tailTrace_7031675
  have hstable : (prefixWord ++ tailWord_7031675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031675).length < 2 ^ (prefixWord ++ tailWord_7031675).sum := by decide
  have hdescent : baseEnd_7031675 < baseStart_7031675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031685 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 1, 8]
def baseStart_7031685 : Nat := 118140960795 + 7031685 * 2 ^ 59
def prefixEnd_7031685 : Nat := 4983230072969 + 3 ^ 40 * 7031685 * 2
def baseEnd_7031685 : Nat := 1203544738670142077933125

theorem tailTrace_7031685 : CollatzResearch.WordTrace tailWord_7031685 prefixEnd_7031685 1203544738670142077933125 := by
  unfold tailWord_7031685
  simp only [CollatzResearch.WordTrace]
  refine ⟨256466621530413636033288509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170977747686942424022192339 256466621530413636033288509)
  ·
    refine ⟨96174983073905113512483191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256466621530413636033288509 96174983073905113512483191)
    ·
      refine ⟨144262474610857670268724787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96174983073905113512483191 144262474610857670268724787)
      ·
        refine ⟨216393711916286505403087181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144262474610857670268724787 216393711916286505403087181)
        ·
          refine ⟨81147641968607439526157693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216393711916286505403087181 81147641968607439526157693)
          ·
            refine ⟨30430365738227789822309135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81147641968607439526157693 30430365738227789822309135)
            ·
              refine ⟨45645548607341684733463703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30430365738227789822309135 45645548607341684733463703)
              ·
                refine ⟨68468322911012527100195555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45645548607341684733463703 68468322911012527100195555)
                ·
                  refine ⟨102702484366518790650293333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68468322911012527100195555 102702484366518790650293333)
                  ·
                    refine ⟨1203544738670142077933125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102702484366518790650293333 1203544738670142077933125)
                    ·
                      rfl

theorem cell23_7031685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_7031685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031685 prefixEnd_7031685 := by exact prefixLift 7031685
  have htrace : WordTrace (prefixWord ++ tailWord_7031685) baseStart_7031685 baseEnd_7031685 := by
    simpa [prefixWord, tailWord_7031685, baseEnd_7031685] using wordTrace_append hprefix tailTrace_7031685
  have hstable : (prefixWord ++ tailWord_7031685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031685).length < 2 ^ (prefixWord ++ tailWord_7031685).sum := by decide
  have hdescent : baseEnd_7031685 < baseStart_7031685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031705 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 3, 4, 4]
def baseStart_7031705 : Nat := 118140960795 + 7031705 * 2 ^ 59
def prefixEnd_7031705 : Nat := 4983230072969 + 3 ^ 40 * 7031705 * 2
def baseEnd_7031705 : Nat := 3610644485623516155549283

theorem tailTrace_7031705 : CollatzResearch.WordTrace tailWord_7031705 prefixEnd_7031705 3610644485623516155549283 := by
  unfold tailWord_7031705
  simp only [CollatzResearch.WordTrace]
  refine ⟨256467350990341179449016569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170978233993560786299344379 256467350990341179449016569)
  ·
    refine ⟨192350513242755884586762427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256467350990341179449016569 192350513242755884586762427)
    ·
      refine ⟨288525769864133826880143641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192350513242755884586762427 288525769864133826880143641)
      ·
        refine ⟨216394327398100370160107731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288525769864133826880143641 216394327398100370160107731)
        ·
          refine ⟨324591491097150555240161597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216394327398100370160107731 324591491097150555240161597)
          ·
            refine ⟨121721809161431458215060599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324591491097150555240161597 121721809161431458215060599)
            ·
              refine ⟨182582713742147187322590899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121721809161431458215060599 182582713742147187322590899)
              ·
                refine ⟨273874070613220780983886349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182582713742147187322590899 273874070613220780983886349)
                ·
                  refine ⟨102702776479957792868957381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 273874070613220780983886349 102702776479957792868957381)
                  ·
                    refine ⟨19256770589992086162929509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102702776479957792868957381 19256770589992086162929509)
                    ·
                      refine ⟨3610644485623516155549283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19256770589992086162929509 3610644485623516155549283)
                      ·
                        rfl

theorem cell23_7031705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_7031705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031705 prefixEnd_7031705 := by exact prefixLift 7031705
  have htrace : WordTrace (prefixWord ++ tailWord_7031705) baseStart_7031705 baseEnd_7031705 := by
    simpa [prefixWord, tailWord_7031705, baseEnd_7031705] using wordTrace_append hprefix tailTrace_7031705
  have hstable : (prefixWord ++ tailWord_7031705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031705).length < 2 ^ (prefixWord ++ tailWord_7031705).sum := by decide
  have hdescent : baseEnd_7031705 < baseStart_7031705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031709 : List Nat := [1, 4, 2, 1, 2, 1, 1, 4, 1, 4, 2]
def baseStart_7031709 : Nat := 118140960795 + 7031709 * 2 ^ 59
def prefixEnd_7031709 : Nat := 4983230072969 + 3 ^ 40 * 7031709 * 2
def baseEnd_7031709 : Nat := 3610646539546134139899265

theorem tailTrace_7031709 : CollatzResearch.WordTrace tailWord_7031709 prefixEnd_7031709 3610646539546134139899265 := by
  unfold tailWord_7031709
  simp only [CollatzResearch.WordTrace]
  refine ⟨256467496882326688132162181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170978331254884458754774787 256467496882326688132162181)
  ·
    refine ⟨48087655665436254024780409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256467496882326688132162181 48087655665436254024780409)
    ·
      refine ⟨36065741749077190518585307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48087655665436254024780409 36065741749077190518585307)
      ·
        refine ⟨54098612623615785777877961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36065741749077190518585307 54098612623615785777877961)
        ·
          refine ⟨40573959467711839333408471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54098612623615785777877961 40573959467711839333408471)
          ·
            refine ⟨60860939201567759000112707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40573959467711839333408471 60860939201567759000112707)
            ·
              refine ⟨91291408802351638500169061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60860939201567759000112707 91291408802351638500169061)
              ·
                refine ⟨17117139150440932218781699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91291408802351638500169061 17117139150440932218781699)
                ·
                  refine ⟨25675708725661398328172549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17117139150440932218781699 25675708725661398328172549)
                  ·
                    refine ⟨4814195386061512186532353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25675708725661398328172549 4814195386061512186532353)
                    ·
                      refine ⟨3610646539546134139899265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4814195386061512186532353 3610646539546134139899265)
                      ·
                        rfl

theorem cell23_7031709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_7031709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031709 prefixEnd_7031709 := by exact prefixLift 7031709
  have htrace : WordTrace (prefixWord ++ tailWord_7031709) baseStart_7031709 baseEnd_7031709 := by
    simpa [prefixWord, tailWord_7031709, baseEnd_7031709] using wordTrace_append hprefix tailTrace_7031709
  have hstable : (prefixWord ++ tailWord_7031709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031709).length < 2 ^ (prefixWord ++ tailWord_7031709).sum := by decide
  have hdescent : baseEnd_7031709 < baseStart_7031709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031713 : List Nat := [1, 2, 3, 4, 1, 1, 4, 1, 1, 3, 2]
def baseStart_7031713 : Nat := 118140960795 + 7031713 * 2 ^ 59
def prefixEnd_7031713 : Nat := 4983230072969 + 3 ^ 40 * 7031713 * 2
def baseEnd_7031713 : Nat := 3610648593468752124249247

theorem tailTrace_7031713 : CollatzResearch.WordTrace tailWord_7031713 prefixEnd_7031713 3610648593468752124249247 := by
  unfold tailWord_7031713
  simp only [CollatzResearch.WordTrace]
  refine ⟨256467642774312196815307793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170978428516208131210205195 256467642774312196815307793)
  ·
    refine ⟨192350732080734147611480845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256467642774312196815307793 192350732080734147611480845)
    ·
      refine ⟨72131524530275305354305317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192350732080734147611480845 72131524530275305354305317)
      ·
        refine ⟨13524660849426619753932247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72131524530275305354305317 13524660849426619753932247)
        ·
          refine ⟨20286991274139929630898371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13524660849426619753932247 20286991274139929630898371)
          ·
            refine ⟨30430486911209894446347557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20286991274139929630898371 30430486911209894446347557)
            ·
              refine ⟨5705716295851855208690167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30430486911209894446347557 5705716295851855208690167)
              ·
                refine ⟨8558574443777782813035251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5705716295851855208690167 8558574443777782813035251)
                ·
                  refine ⟨12837861665666674219552877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8558574443777782813035251 12837861665666674219552877)
                  ·
                    refine ⟨4814198124625002832332329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12837861665666674219552877 4814198124625002832332329)
                    ·
                      refine ⟨3610648593468752124249247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4814198124625002832332329 3610648593468752124249247)
                      ·
                        rfl

theorem cell23_7031713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_7031713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031713 prefixEnd_7031713 := by exact prefixLift 7031713
  have htrace : WordTrace (prefixWord ++ tailWord_7031713) baseStart_7031713 baseEnd_7031713 := by
    simpa [prefixWord, tailWord_7031713, baseEnd_7031713] using wordTrace_append hprefix tailTrace_7031713
  have hstable : (prefixWord ++ tailWord_7031713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031713).length < 2 ^ (prefixWord ++ tailWord_7031713).sum := by decide
  have hdescent : baseEnd_7031713 < baseStart_7031713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031794 : List Nat := [3, 2, 1, 5, 2, 1, 2, 1, 2, 2, 2]
def baseStart_7031794 : Nat := 118140960795 + 7031794 * 2 ^ 59
def prefixEnd_7031794 : Nat := 4983230072969 + 3 ^ 40 * 7031794 * 2
def baseEnd_7031794 : Nat := 3610690185401766307336375

theorem tailTrace_7031794 : CollatzResearch.WordTrace tailWord_7031794 prefixEnd_7031794 3610690185401766307336375 := by
  unfold tailWord_7031794
  simp only [CollatzResearch.WordTrace]
  refine ⟨64117649271754686912251609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170980398058012498432670957 64117649271754686912251609)
  ·
    refine ⟨48088236953816015184188707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64117649271754686912251609 48088236953816015184188707)
    ·
      refine ⟨72132355430724022776283061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48088236953816015184188707 72132355430724022776283061)
      ·
        refine ⟨6762408321630377135276537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72132355430724022776283061 6762408321630377135276537)
        ·
          refine ⟨5071806241222782851457403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6762408321630377135276537 5071806241222782851457403)
          ·
            refine ⟨7607709361834174277186105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5071806241222782851457403 7607709361834174277186105)
            ·
              refine ⟨5705782021375630707889579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7607709361834174277186105 5705782021375630707889579)
              ·
                refine ⟨8558673032063446061834369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5705782021375630707889579 8558673032063446061834369)
                ·
                  refine ⟨6419004774047584546375777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8558673032063446061834369 6419004774047584546375777)
                  ·
                    refine ⟨4814253580535688409781833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6419004774047584546375777 4814253580535688409781833)
                    ·
                      refine ⟨3610690185401766307336375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4814253580535688409781833 3610690185401766307336375)
                      ·
                        rfl

theorem cell23_7031794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_7031794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031794 prefixEnd_7031794 := by exact prefixLift 7031794
  have htrace : WordTrace (prefixWord ++ tailWord_7031794) baseStart_7031794 baseEnd_7031794 := by
    simpa [prefixWord, tailWord_7031794, baseEnd_7031794] using wordTrace_append hprefix tailTrace_7031794
  have hstable : (prefixWord ++ tailWord_7031794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031794).length < 2 ^ (prefixWord ++ tailWord_7031794).sum := by decide
  have hdescent : baseEnd_7031794 < baseStart_7031794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031802 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3]
def baseStart_7031802 : Nat := 118140960795 + 7031802 * 2 ^ 59
def prefixEnd_7031802 : Nat := 4983230072969 + 3 ^ 40 * 7031802 * 2
def baseEnd_7031802 : Nat := 3610694293247002276036337

theorem tailTrace_7031802 : CollatzResearch.WordTrace tailWord_7031802 prefixEnd_7031802 3610694293247002276036337 := by
  unfold tailWord_7031802
  simp only [CollatzResearch.WordTrace]
  refine ⟨64117722217747441253824415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170980592580659843343531773 64117722217747441253824415)
  ·
    refine ⟨96176583326621161880736623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64117722217747441253824415 96176583326621161880736623)
    ·
      refine ⟨144264874989931742821104935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96176583326621161880736623 144264874989931742821104935)
      ·
        refine ⟨216397312484897614231657403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144264874989931742821104935 216397312484897614231657403)
        ·
          refine ⟨324595968727346421347486105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216397312484897614231657403 324595968727346421347486105)
          ·
            refine ⟨243446976545509816010614579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324595968727346421347486105 243446976545509816010614579)
            ·
              refine ⟨365170464818264724015921869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243446976545509816010614579 365170464818264724015921869)
              ·
                refine ⟨136938924306849271505970701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365170464818264724015921869 136938924306849271505970701)
                ·
                  refine ⟨51352096615068476814739013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136938924306849271505970701 51352096615068476814739013)
                  ·
                    refine ⟨9628518115325339402763565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51352096615068476814739013 9628518115325339402763565)
                    ·
                      refine ⟨3610694293247002276036337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9628518115325339402763565 3610694293247002276036337)
                      ·
                        rfl

theorem cell23_7031802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3].length) (baseStart_7031802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031802 prefixEnd_7031802 := by exact prefixLift 7031802
  have htrace : WordTrace (prefixWord ++ tailWord_7031802) baseStart_7031802 baseEnd_7031802 := by
    simpa [prefixWord, tailWord_7031802, baseEnd_7031802] using wordTrace_append hprefix tailTrace_7031802
  have hstable : (prefixWord ++ tailWord_7031802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031802).length < 2 ^ (prefixWord ++ tailWord_7031802).sum := by decide
  have hdescent : baseEnd_7031802 < baseStart_7031802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031819 : List Nat := [1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 3]
def baseStart_7031819 : Nat := 118140960795 + 7031819 * 2 ^ 59
def prefixEnd_7031819 : Nat := 4983230072969 + 3 ^ 40 * 7031819 * 2
def baseEnd_7031819 : Nat := 3610703022418128709523759

theorem tailTrace_7031819 : CollatzResearch.WordTrace tailWord_7031819 prefixEnd_7031819 3610703022418128709523759 := by
  unfold tailWord_7031819
  simp only [CollatzResearch.WordTrace]
  refine ⟨256471508911928176918666511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170981005941285451279111007 256471508911928176918666511)
  ·
    refine ⟨384707263367892265377999767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256471508911928176918666511 384707263367892265377999767)
    ·
      refine ⟨577060895051838398066999651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384707263367892265377999767 577060895051838398066999651)
      ·
        refine ⟨865591342577757597100499477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577060895051838398066999651 865591342577757597100499477)
        ·
          refine ⟨40574594183332387364085913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 865591342577757597100499477 40574594183332387364085913)
          ·
            refine ⟨30430945637499290523064435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40574594183332387364085913 30430945637499290523064435)
            ·
              refine ⟨45646418456248935784596653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30430945637499290523064435 45646418456248935784596653)
              ·
                refine ⟨17117406921093350919223745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45646418456248935784596653 17117406921093350919223745)
                ·
                  refine ⟨12838055190820013189417809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17117406921093350919223745 12838055190820013189417809)
                  ·
                    refine ⟨9628541393115009892063357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12838055190820013189417809 9628541393115009892063357)
                    ·
                      refine ⟨3610703022418128709523759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9628541393115009892063357 3610703022418128709523759)
                      ·
                        rfl

theorem cell23_7031819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 3].length) (baseStart_7031819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031819 prefixEnd_7031819 := by exact prefixLift 7031819
  have htrace : WordTrace (prefixWord ++ tailWord_7031819) baseStart_7031819 baseEnd_7031819 := by
    simpa [prefixWord, tailWord_7031819, baseEnd_7031819] using wordTrace_append hprefix tailTrace_7031819
  have hstable : (prefixWord ++ tailWord_7031819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031819).length < 2 ^ (prefixWord ++ tailWord_7031819).sum := by decide
  have hdescent : baseEnd_7031819 < baseStart_7031819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031839 : List Nat := [1, 1, 2, 4, 1, 4, 2, 2, 6]
def baseStart_7031839 : Nat := 118140960795 + 7031839 * 2 ^ 59
def prefixEnd_7031839 : Nat := 4983230072969 + 3 ^ 40 * 7031839 * 2
def baseEnd_7031839 : Nat := 401190365781246514585963

theorem tailTrace_7031839 : CollatzResearch.WordTrace tailWord_7031839 prefixEnd_7031839 401190365781246514585963 := by
  unfold tailWord_7031839
  simp only [CollatzResearch.WordTrace]
  refine ⟨256472238371855720334394571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170981492247903813556263047 256472238371855720334394571)
  ·
    refine ⟨384708357557783580501591857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256472238371855720334394571 384708357557783580501591857)
    ·
      refine ⟨288531268168337685376193893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384708357557783580501591857 288531268168337685376193893)
      ·
        refine ⟨54099612781563316008036355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 288531268168337685376193893 54099612781563316008036355)
        ·
          refine ⟨81149419172344974012054533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54099612781563316008036355 81149419172344974012054533)
          ·
            refine ⟨15215516094814682627260225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81149419172344974012054533 15215516094814682627260225)
            ·
              refine ⟨11411637071111011970445169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15215516094814682627260225 11411637071111011970445169)
              ·
                refine ⟨8558727803333258977833877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11411637071111011970445169 8558727803333258977833877)
                ·
                  refine ⟨401190365781246514585963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8558727803333258977833877 401190365781246514585963)
                  ·
                    rfl

theorem cell23_7031839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 6].length) (baseStart_7031839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031839 prefixEnd_7031839 := by exact prefixLift 7031839
  have htrace : WordTrace (prefixWord ++ tailWord_7031839) baseStart_7031839 baseEnd_7031839 := by
    simpa [prefixWord, tailWord_7031839, baseEnd_7031839] using wordTrace_append hprefix tailTrace_7031839
  have hstable : (prefixWord ++ tailWord_7031839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031839).length < 2 ^ (prefixWord ++ tailWord_7031839).sum := by decide
  have hdescent : baseEnd_7031839 < baseStart_7031839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031843 : List Nat := [1, 1, 1, 4, 3, 2, 4, 2, 1, 4]
def baseStart_7031843 : Nat := 118140960795 + 7031843 * 2 ^ 59
def prefixEnd_7031843 : Nat := 4983230072969 + 3 ^ 40 * 7031843 * 2
def baseEnd_7031843 : Nat := 1203571781984612205207883

theorem tailTrace_7031843 : CollatzResearch.WordTrace tailWord_7031843 prefixEnd_7031843 1203571781984612205207883 := by
  unfold tailWord_7031843
  simp only [CollatzResearch.WordTrace]
  refine ⟨256472384263841229017540183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170981589509227486011693455 256472384263841229017540183)
  ·
    refine ⟨384708576395761843526310275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256472384263841229017540183 384708576395761843526310275)
    ·
      refine ⟨577062864593642765289465413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384708576395761843526310275 577062864593642765289465413)
      ·
        refine ⟨108199287111308018491774765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 577062864593642765289465413 108199287111308018491774765)
        ·
          refine ⟨40574732666740506934415537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108199287111308018491774765 40574732666740506934415537)
          ·
            refine ⟨30431049500055380200811653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40574732666740506934415537 30431049500055380200811653)
            ·
              refine ⟨5705821781260383787652185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30431049500055380200811653 5705821781260383787652185)
              ·
                refine ⟨4279366335945287840739139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5705821781260383787652185 4279366335945287840739139)
                ·
                  refine ⟨6419049503917931761108709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4279366335945287840739139 6419049503917931761108709)
                  ·
                    refine ⟨1203571781984612205207883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6419049503917931761108709 1203571781984612205207883)
                    ·
                      rfl

theorem cell23_7031843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 1, 4].length) (baseStart_7031843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031843 prefixEnd_7031843 := by exact prefixLift 7031843
  have htrace : WordTrace (prefixWord ++ tailWord_7031843) baseStart_7031843 baseEnd_7031843 := by
    simpa [prefixWord, tailWord_7031843, baseEnd_7031843] using wordTrace_append hprefix tailTrace_7031843
  have hstable : (prefixWord ++ tailWord_7031843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031843).length < 2 ^ (prefixWord ++ tailWord_7031843).sum := by decide
  have hdescent : baseEnd_7031843 < baseStart_7031843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031852 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 5, 5]
def baseStart_7031852 : Nat := 118140960795 + 7031852 * 2 ^ 59
def prefixEnd_7031852 : Nat := 4983230072969 + 3 ^ 40 * 7031852 * 2
def baseEnd_7031852 : Nat := 1203573322426575693470369

theorem tailTrace_7031852 : CollatzResearch.WordTrace tailWord_7031852 prefixEnd_7031852 1203573322426575693470369 := by
  unfold tailWord_7031852
  simp only [CollatzResearch.WordTrace]
  refine ⟨128236356260404311777308905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170981808347205749036411873 128236356260404311777308905)
  ·
    refine ⟨96177267195303233832981679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128236356260404311777308905 96177267195303233832981679)
    ·
      refine ⟨144265900792954850749472519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96177267195303233832981679 144265900792954850749472519)
      ·
        refine ⟨216398851189432276124208779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144265900792954850749472519 216398851189432276124208779)
        ·
          refine ⟨324598276784148414186313169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216398851189432276124208779 324598276784148414186313169)
          ·
            refine ⟨243448707588111310639734877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324598276784148414186313169 243448707588111310639734877)
            ·
              refine ⟨91293265345541741489900579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243448707588111310639734877 91293265345541741489900579)
              ·
                refine ⟨136939898018312612234850869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91293265345541741489900579 136939898018312612234850869)
                ·
                  refine ⟨12838115439216807397017269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136939898018312612234850869 12838115439216807397017269)
                  ·
                    refine ⟨1203573322426575693470369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12838115439216807397017269 1203573322426575693470369)
                    ·
                      rfl

theorem cell23_7031852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 5].length) (baseStart_7031852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031852 prefixEnd_7031852 := by exact prefixLift 7031852
  have htrace : WordTrace (prefixWord ++ tailWord_7031852) baseStart_7031852 baseEnd_7031852 := by
    simpa [prefixWord, tailWord_7031852, baseEnd_7031852] using wordTrace_append hprefix tailTrace_7031852
  have hstable : (prefixWord ++ tailWord_7031852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031852).length < 2 ^ (prefixWord ++ tailWord_7031852).sum := by decide
  have hdescent : baseEnd_7031852 < baseStart_7031852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031859 : List Nat := [1, 1, 1, 2, 4, 1, 1, 4, 1, 5, 2]
def baseStart_7031859 : Nat := 118140960795 + 7031859 * 2 ^ 59
def prefixEnd_7031859 : Nat := 4983230072969 + 3 ^ 40 * 7031859 * 2
def baseEnd_7031859 : Nat := 3610723561644308553023575

theorem tailTrace_7031859 : CollatzResearch.WordTrace tailWord_7031859 prefixEnd_7031859 3610723561644308553023575 := by
  unfold tailWord_7031859
  simp only [CollatzResearch.WordTrace]
  refine ⟨256472967831783263750122631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170981978554522175833415087 256472967831783263750122631)
  ·
    refine ⟨384709451747674895625183947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256472967831783263750122631 384709451747674895625183947)
    ·
      refine ⟨577064177621512343437775921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384709451747674895625183947 577064177621512343437775921)
      ·
        refine ⟨432798133216134257578331941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577064177621512343437775921 432798133216134257578331941)
        ·
          refine ⟨81149649978025173295937239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 432798133216134257578331941 81149649978025173295937239)
          ·
            refine ⟨121724474967037759943905859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81149649978025173295937239 121724474967037759943905859)
            ·
              refine ⟨182586712450556639915858789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121724474967037759943905859 182586712450556639915858789)
              ·
                refine ⟨34235008584479369984223523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182586712450556639915858789 34235008584479369984223523)
                ·
                  refine ⟨51352512876719054976335285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34235008584479369984223523 51352512876719054976335285)
                  ·
                    refine ⟨4814298082192411404031433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51352512876719054976335285 4814298082192411404031433)
                    ·
                      refine ⟨3610723561644308553023575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4814298082192411404031433 3610723561644308553023575)
                      ·
                        rfl

theorem cell23_7031859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 5, 2].length) (baseStart_7031859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031859 prefixEnd_7031859 := by exact prefixLift 7031859
  have htrace : WordTrace (prefixWord ++ tailWord_7031859) baseStart_7031859 baseEnd_7031859 := by
    simpa [prefixWord, tailWord_7031859, baseEnd_7031859] using wordTrace_append hprefix tailTrace_7031859
  have hstable : (prefixWord ++ tailWord_7031859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031859).length < 2 ^ (prefixWord ++ tailWord_7031859).sum := by decide
  have hdescent : baseEnd_7031859 < baseStart_7031859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031869 : List Nat := [1, 4, 1, 3, 1, 2, 2, 1, 3, 5]
def baseStart_7031869 : Nat := 118140960795 + 7031869 * 2 ^ 59
def prefixEnd_7031869 : Nat := 4983230072969 + 3 ^ 40 * 7031869 * 2
def baseEnd_7031869 : Nat := 1203576232150284504632843

theorem tailTrace_7031869 : CollatzResearch.WordTrace tailWord_7031869 prefixEnd_7031869 1203576232150284504632843 := by
  unfold tailWord_7031869
  simp only [CollatzResearch.WordTrace]
  refine ⟨256473332561747035457986661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170982221707831356971991107 256473332561747035457986661)
  ·
    refine ⟨48088749855327569148372499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256473332561747035457986661 48088749855327569148372499)
    ·
      refine ⟨72133124782991353722558749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48088749855327569148372499 72133124782991353722558749)
      ·
        refine ⟨27049921793621757645959531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72133124782991353722558749 27049921793621757645959531)
        ·
          refine ⟨40574882690432636468939297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27049921793621757645959531 40574882690432636468939297)
          ·
            refine ⟨30431162017824477351704473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40574882690432636468939297 30431162017824477351704473)
            ·
              refine ⟨22823371513368358013778355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30431162017824477351704473 22823371513368358013778355)
              ·
                refine ⟨34235057270052537020667533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22823371513368358013778355 34235057270052537020667533)
                ·
                  refine ⟨12838146476269701382750325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34235057270052537020667533 12838146476269701382750325)
                  ·
                    refine ⟨1203576232150284504632843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12838146476269701382750325 1203576232150284504632843)
                    ·
                      rfl

theorem cell23_7031869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_7031869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031869 prefixEnd_7031869 := by exact prefixLift 7031869
  have htrace : WordTrace (prefixWord ++ tailWord_7031869) baseStart_7031869 baseEnd_7031869 := by
    simpa [prefixWord, tailWord_7031869, baseEnd_7031869] using wordTrace_append hprefix tailTrace_7031869
  have hstable : (prefixWord ++ tailWord_7031869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031869).length < 2 ^ (prefixWord ++ tailWord_7031869).sum := by decide
  have hdescent : baseEnd_7031869 < baseStart_7031869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031909 : List Nat := [1, 3, 1, 3, 2, 1, 3, 2, 1, 1, 5]
def baseStart_7031909 : Nat := 118140960795 + 7031909 * 2 ^ 59
def prefixEnd_7031909 : Nat := 4983230072969 + 3 ^ 40 * 7031909 * 2
def baseEnd_7031909 : Nat := 3610749235677033357398345

theorem tailTrace_7031909 : CollatzResearch.WordTrace tailWord_7031909 prefixEnd_7031909 3610749235677033357398345 := by
  unfold tailWord_7031909
  simp only [CollatzResearch.WordTrace]
  refine ⟨256474791481602122289442781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170983194321068081526295187 256474791481602122289442781)
  ·
    refine ⟨96178046805600795858541043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256474791481602122289442781 96178046805600795858541043)
    ·
      refine ⟨144267070208401193787811565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96178046805600795858541043 144267070208401193787811565)
      ·
        refine ⟨54100151328150447670429337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144267070208401193787811565 54100151328150447670429337)
        ·
          refine ⟨40575113496112835752822003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54100151328150447670429337 40575113496112835752822003)
          ·
            refine ⟨60862670244169253629233005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40575113496112835752822003 60862670244169253629233005)
            ·
              refine ⟨22823501341563470110962377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60862670244169253629233005 22823501341563470110962377)
              ·
                refine ⟨17117626006172602583221783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22823501341563470110962377 17117626006172602583221783)
                ·
                  refine ⟨25676439009258903874832675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17117626006172602583221783 25676439009258903874832675)
                  ·
                    refine ⟨38514658513888355812249013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25676439009258903874832675 38514658513888355812249013)
                    ·
                      refine ⟨3610749235677033357398345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38514658513888355812249013 3610749235677033357398345)
                      ·
                        rfl

theorem cell23_7031909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_7031909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031909 prefixEnd_7031909 := by exact prefixLift 7031909
  have htrace : WordTrace (prefixWord ++ tailWord_7031909) baseStart_7031909 baseEnd_7031909 := by
    simpa [prefixWord, tailWord_7031909, baseEnd_7031909] using wordTrace_append hprefix tailTrace_7031909
  have hstable : (prefixWord ++ tailWord_7031909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031909).length < 2 ^ (prefixWord ++ tailWord_7031909).sum := by decide
  have hdescent : baseEnd_7031909 < baseStart_7031909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031929 : List Nat := [1, 2, 1, 3, 5, 1, 1, 9]
def baseStart_7031929 : Nat := 118140960795 + 7031929 * 2 ^ 59
def prefixEnd_7031929 : Nat := 4983230072969 + 3 ^ 40 * 7031929 * 2
def baseEnd_7031929 : Nat := 133731833529263825153639

theorem tailTrace_7031929 : CollatzResearch.WordTrace tailWord_7031929 prefixEnd_7031929 133731833529263825153639 := by
  unfold tailWord_7031929
  simp only [CollatzResearch.WordTrace]
  refine ⟨256475520941529665705170841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170983680627686443803447227 256475520941529665705170841)
  ·
    refine ⟨192356640706147249278878131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256475520941529665705170841 192356640706147249278878131)
    ·
      refine ⟨288534961059220873918317197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192356640706147249278878131 288534961059220873918317197)
      ·
        refine ⟨108200610397207827719368949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288534961059220873918317197 108200610397207827719368949)
        ·
          refine ⟨10143807224738233848690839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108200610397207827719368949 10143807224738233848690839)
          ·
            refine ⟨15215710837107350773036259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10143807224738233848690839 15215710837107350773036259)
            ·
              refine ⟨22823566255661026159554389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15215710837107350773036259 22823566255661026159554389)
              ·
                refine ⟨133731833529263825153639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22823566255661026159554389 133731833529263825153639)
                ·
                  rfl

theorem cell23_7031929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 9].length) (baseStart_7031929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031929 prefixEnd_7031929 := by exact prefixLift 7031929
  have htrace : WordTrace (prefixWord ++ tailWord_7031929) baseStart_7031929 baseEnd_7031929 := by
    simpa [prefixWord, tailWord_7031929, baseEnd_7031929] using wordTrace_append hprefix tailTrace_7031929
  have hstable : (prefixWord ++ tailWord_7031929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031929).length < 2 ^ (prefixWord ++ tailWord_7031929).sum := by decide
  have hdescent : baseEnd_7031929 < baseStart_7031929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031939 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 3]
def baseStart_7031939 : Nat := 118140960795 + 7031939 * 2 ^ 59
def prefixEnd_7031939 : Nat := 4983230072969 + 3 ^ 40 * 7031939 * 2
def baseEnd_7031939 : Nat := 3610764640096668240023207

theorem tailTrace_7031939 : CollatzResearch.WordTrace tailWord_7031939 prefixEnd_7031939 3610764640096668240023207 := by
  unfold tailWord_7031939
  simp only [CollatzResearch.WordTrace]
  refine ⟨256475885671493437413034871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170983923780995624942023247 256475885671493437413034871)
  ·
    refine ⟨384713828507240156119552307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256475885671493437413034871 384713828507240156119552307)
    ·
      refine ⟨577070742760860234179328461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384713828507240156119552307 577070742760860234179328461)
      ·
        refine ⟨216401528535322587817248173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 577070742760860234179328461 216401528535322587817248173)
        ·
          refine ⟨81150573200745970431468065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216401528535322587817248173 81150573200745970431468065)
          ·
            refine ⟨60862929900559477823601049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81150573200745970431468065 60862929900559477823601049)
            ·
              refine ⟨45647197425419608367700787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60862929900559477823601049 45647197425419608367700787)
              ·
                refine ⟨68470796138129412551551181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45647197425419608367700787 68470796138129412551551181)
                ·
                  refine ⟨25676548551798529706831693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68470796138129412551551181 25676548551798529706831693)
                  ·
                    refine ⟨9628705706924448640061885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25676548551798529706831693 9628705706924448640061885)
                    ·
                      refine ⟨3610764640096668240023207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9628705706924448640061885 3610764640096668240023207)
                      ·
                        rfl

theorem cell23_7031939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 3].length) (baseStart_7031939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031939 prefixEnd_7031939 := by exact prefixLift 7031939
  have htrace : WordTrace (prefixWord ++ tailWord_7031939) baseStart_7031939 baseEnd_7031939 := by
    simpa [prefixWord, tailWord_7031939, baseEnd_7031939] using wordTrace_append hprefix tailTrace_7031939
  have hstable : (prefixWord ++ tailWord_7031939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031939).length < 2 ^ (prefixWord ++ tailWord_7031939).sum := by decide
  have hdescent : baseEnd_7031939 < baseStart_7031939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031967 : List Nat := [1, 1, 2, 6, 3, 1, 2, 1, 2, 4]
def baseStart_7031967 : Nat := 118140960795 + 7031967 * 2 ^ 59
def prefixEnd_7031967 : Nat := 4983230072969 + 3 ^ 40 * 7031967 * 2
def baseEnd_7031967 : Nat := 1203593005851664710157693

theorem tailTrace_7031967 : CollatzResearch.WordTrace tailWord_7031967 prefixEnd_7031967 1203593005851664710157693 := by
  unfold tailWord_7031967
  simp only [CollatzResearch.WordTrace]
  refine ⟨256476906915391998195054155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170984604610261332130036103 256476906915391998195054155)
  ·
    refine ⟨384715360373087997292581233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256476906915391998195054155 384715360373087997292581233)
    ·
      refine ⟨288536520279815997969435925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384715360373087997292581233 288536520279815997969435925)
      ·
        refine ⟨13525149388116374904817309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 288536520279815997969435925 13525149388116374904817309)
        ·
          refine ⟨5071931020543640589306491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13525149388116374904817309 5071931020543640589306491)
          ·
            refine ⟨7607896530815460883959737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5071931020543640589306491 7607896530815460883959737)
            ·
              refine ⟨5705922398111595662969803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7607896530815460883959737 5705922398111595662969803)
              ·
                refine ⟨8558883597167393494454705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5705922398111595662969803 8558883597167393494454705)
                ·
                  refine ⟨6419162697875545120841029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8558883597167393494454705 6419162697875545120841029)
                  ·
                    refine ⟨1203593005851664710157693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6419162697875545120841029 1203593005851664710157693)
                    ·
                      rfl

theorem cell23_7031967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 2, 4].length) (baseStart_7031967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031967 prefixEnd_7031967 := by exact prefixLift 7031967
  have htrace : WordTrace (prefixWord ++ tailWord_7031967) baseStart_7031967 baseEnd_7031967 := by
    simpa [prefixWord, tailWord_7031967, baseEnd_7031967] using wordTrace_append hprefix tailTrace_7031967
  have hstable : (prefixWord ++ tailWord_7031967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031967).length < 2 ^ (prefixWord ++ tailWord_7031967).sum := by decide
  have hdescent : baseEnd_7031967 < baseStart_7031967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031973 : List Nat := [1, 3, 1, 2, 1, 5, 1, 3, 2, 1, 3]
def baseStart_7031973 : Nat := 118140960795 + 7031973 * 2 ^ 59
def prefixEnd_7031973 : Nat := 4983230072969 + 3 ^ 40 * 7031973 * 2
def baseEnd_7031973 : Nat := 3610782098438921106998051

theorem tailTrace_7031973 : CollatzResearch.WordTrace tailWord_7031973 prefixEnd_7031973 3610782098438921106998051 := by
  unfold tailWord_7031973
  simp only [CollatzResearch.WordTrace]
  refine ⟨256477125753370261219772573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170984750502246840813181715 256477125753370261219772573)
  ·
    refine ⟨96178922157513847957414715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256477125753370261219772573 96178922157513847957414715)
    ·
      refine ⟨144268383236270771936122073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96178922157513847957414715 144268383236270771936122073)
      ·
        refine ⟨108201287427203078952091555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144268383236270771936122073 108201287427203078952091555)
        ·
          refine ⟨162301931140804618428137333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108201287427203078952091555 162301931140804618428137333)
          ·
            refine ⟨15215806044450432977637875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162301931140804618428137333 15215806044450432977637875)
            ·
              refine ⟨22823709066675649466456813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15215806044450432977637875 22823709066675649466456813)
              ·
                refine ⟨8558890900003368549921305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22823709066675649466456813 8558890900003368549921305)
                ·
                  refine ⟨6419168175002526412440979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8558890900003368549921305 6419168175002526412440979)
                  ·
                    refine ⟨9628752262503789618661469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6419168175002526412440979 9628752262503789618661469)
                    ·
                      refine ⟨3610782098438921106998051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9628752262503789618661469 3610782098438921106998051)
                      ·
                        rfl

theorem cell23_7031973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_7031973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031973 prefixEnd_7031973 := by exact prefixLift 7031973
  have htrace : WordTrace (prefixWord ++ tailWord_7031973) baseStart_7031973 baseEnd_7031973 := by
    simpa [prefixWord, tailWord_7031973, baseEnd_7031973] using wordTrace_append hprefix tailTrace_7031973
  have hstable : (prefixWord ++ tailWord_7031973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031973).length < 2 ^ (prefixWord ++ tailWord_7031973).sum := by decide
  have hdescent : baseEnd_7031973 < baseStart_7031973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031983 : List Nat := [1, 1, 2, 1, 2, 3, 5, 2, 1, 3, 2]
def baseStart_7031983 : Nat := 118140960795 + 7031983 * 2 ^ 59
def prefixEnd_7031983 : Nat := 4983230072969 + 3 ^ 40 * 7031983 * 2
def baseEnd_7031983 : Nat := 3610787233245466067873005

theorem tailTrace_7031983 : CollatzResearch.WordTrace tailWord_7031983 prefixEnd_7031983 3610787233245466067873005 := by
  unfold tailWord_7031983
  simp only [CollatzResearch.WordTrace]
  refine ⟨256477490483334032927636603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170984993655556021951757735 256477490483334032927636603)
  ·
    refine ⟨384716235725001049391454905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256477490483334032927636603 384716235725001049391454905)
    ·
      refine ⟨288537176793750787043591179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384716235725001049391454905 288537176793750787043591179)
      ·
        refine ⟨432805765190626180565386769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288537176793750787043591179 432805765190626180565386769)
        ·
          refine ⟨324604323892969635424040077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 432805765190626180565386769 324604323892969635424040077)
          ·
            refine ⟨121726621459863613284015029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324604323892969635424040077 121726621459863613284015029)
            ·
              refine ⟨11411870761862213745376409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121726621459863613284015029 11411870761862213745376409)
              ·
                refine ⟨8558903071396660309032307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11411870761862213745376409 8558903071396660309032307)
                ·
                  refine ⟨12838354607094990463548461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8558903071396660309032307 12838354607094990463548461)
                  ·
                    refine ⟨4814382977660621423830673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12838354607094990463548461 4814382977660621423830673)
                    ·
                      refine ⟨3610787233245466067873005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4814382977660621423830673 3610787233245466067873005)
                      ·
                        rfl

theorem cell23_7031983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 3, 2].length) (baseStart_7031983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031983 prefixEnd_7031983 := by exact prefixLift 7031983
  have htrace : WordTrace (prefixWord ++ tailWord_7031983) baseStart_7031983 baseEnd_7031983 := by
    simpa [prefixWord, tailWord_7031983, baseEnd_7031983] using wordTrace_append hprefix tailTrace_7031983
  have hstable : (prefixWord ++ tailWord_7031983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031983).length < 2 ^ (prefixWord ++ tailWord_7031983).sum := by decide
  have hdescent : baseEnd_7031983 < baseStart_7031983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7031999 : List Nat := [1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 5]
def baseStart_7031999 : Nat := 118140960795 + 7031999 * 2 ^ 59
def prefixEnd_7031999 : Nat := 4983230072969 + 3 ^ 40 * 7031999 * 2
def baseEnd_7031999 : Nat := 3610795448935938005272931

theorem tailTrace_7031999 : CollatzResearch.WordTrace tailWord_7031999 prefixEnd_7031999 3610795448935938005272931 := by
  unfold tailWord_7031999
  simp only [CollatzResearch.WordTrace]
  refine ⟨256478074051276067660219051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170985382700850711773479367 256478074051276067660219051)
  ·
    refine ⟨384717111076914101490328577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256478074051276067660219051 384717111076914101490328577)
    ·
      refine ⟨288537833307685576117746433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384717111076914101490328577 288537833307685576117746433)
      ·
        refine ⟨216403374980764182088309825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288537833307685576117746433 216403374980764182088309825)
        ·
          refine ⟨162302531235573136566232369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216403374980764182088309825 162302531235573136566232369)
          ·
            refine ⟨121726898426679852424674277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162302531235573136566232369 121726898426679852424674277)
            ·
              refine ⟨22823793455002472329626427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121726898426679852424674277 22823793455002472329626427)
              ·
                refine ⟨34235690182503708494439641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22823793455002472329626427 34235690182503708494439641)
                ·
                  refine ⟨25676767636877781370829731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34235690182503708494439641 25676767636877781370829731)
                  ·
                    refine ⟨38515151455316672056244597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25676767636877781370829731 38515151455316672056244597)
                    ·
                      refine ⟨3610795448935938005272931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38515151455316672056244597 3610795448935938005272931)
                      ·
                        rfl

theorem cell23_7031999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_7031999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7031999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7031999 prefixEnd_7031999 := by exact prefixLift 7031999
  have htrace : WordTrace (prefixWord ++ tailWord_7031999) baseStart_7031999 baseEnd_7031999 := by
    simpa [prefixWord, tailWord_7031999, baseEnd_7031999] using wordTrace_append hprefix tailTrace_7031999
  have hstable : (prefixWord ++ tailWord_7031999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7031999).length < 2 ^ (prefixWord ++ tailWord_7031999).sum := by decide
  have hdescent : baseEnd_7031999 < baseStart_7031999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7031999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032126 : List Nat := [4, 2, 1, 2, 1, 1, 1, 3, 8]
def baseStart_7032126 : Nat := 118140960795 + 7032126 * 2 ^ 59
def prefixEnd_7032126 : Nat := 4983230072969 + 3 ^ 40 * 7032126 * 2
def baseEnd_7032126 : Nat := 401206740108784334264983

theorem tailTrace_7032126 : CollatzResearch.WordTrace tailWord_7032126 prefixEnd_7032126 401206740108784334264983 := by
  unfold tailWord_7032126
  simp only [CollatzResearch.WordTrace]
  refine ⟨32060338265226996043761529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170988470747877312233394821 32060338265226996043761529)
  ·
    refine ⟨24045253698920247032821147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32060338265226996043761529 24045253698920247032821147)
    ·
      refine ⟨36067880548380370549231721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24045253698920247032821147 36067880548380370549231721)
      ·
        refine ⟨27050910411285277911923791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36067880548380370549231721 27050910411285277911923791)
        ·
          refine ⟨40576365616927916867885687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27050910411285277911923791 40576365616927916867885687)
          ·
            refine ⟨60864548425391875301828531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40576365616927916867885687 60864548425391875301828531)
            ·
              refine ⟨91296822638087812952742797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60864548425391875301828531 91296822638087812952742797)
              ·
                refine ⟨34236308489282929857278549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91296822638087812952742797 34236308489282929857278549)
                ·
                  refine ⟨401206740108784334264983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34236308489282929857278549 401206740108784334264983)
                  ·
                    rfl

theorem cell23_7032126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_7032126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032126 prefixEnd_7032126 := by exact prefixLift 7032126
  have htrace : WordTrace (prefixWord ++ tailWord_7032126) baseStart_7032126 baseEnd_7032126 := by
    simpa [prefixWord, tailWord_7032126, baseEnd_7032126] using wordTrace_append hprefix tailTrace_7032126
  have hstable : (prefixWord ++ tailWord_7032126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032126).length < 2 ^ (prefixWord ++ tailWord_7032126).sum := by decide
  have hdescent : baseEnd_7032126 < baseStart_7032126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032153 : List Nat := [1, 2, 1, 2, 2, 2, 2, 4, 3, 1, 3]
def baseStart_7032153 : Nat := 118140960795 + 7032153 * 2 ^ 59
def prefixEnd_7032153 : Nat := 4983230072969 + 3 ^ 40 * 7032153 * 2
def baseEnd_7032153 : Nat := 3610874524956730402747223

theorem tailTrace_7032153 : CollatzResearch.WordTrace tailWord_7032153 prefixEnd_7032153 3610874524956730402747223 := by
  unfold tailWord_7032153
  simp only [CollatzResearch.WordTrace]
  refine ⟨256483690892718151961325113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170989127261812101307550075 256483690892718151961325113)
  ·
    refine ⟨192362768169538613970993835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256483690892718151961325113 192362768169538613970993835)
    ·
      refine ⟨288544152254307920956490753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192362768169538613970993835 288544152254307920956490753)
      ·
        refine ⟨216408114190730940717368065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288544152254307920956490753 216408114190730940717368065)
        ·
          refine ⟨162306085643048205538026049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216408114190730940717368065 162306085643048205538026049)
          ·
            refine ⟨121729564232286154153519537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162306085643048205538026049 121729564232286154153519537)
            ·
              refine ⟨91297173174214615615139653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121729564232286154153519537 91297173174214615615139653)
              ·
                refine ⟨17118219970165240427838685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91297173174214615615139653 17118219970165240427838685)
                ·
                  refine ⟨6419332488811965160439507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17118219970165240427838685 6419332488811965160439507)
                  ·
                    refine ⟨9628998733217947740659261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6419332488811965160439507 9628998733217947740659261)
                    ·
                      refine ⟨3610874524956730402747223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9628998733217947740659261 3610874524956730402747223)
                      ·
                        rfl

theorem cell23_7032153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 1, 3].length) (baseStart_7032153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032153 prefixEnd_7032153 := by exact prefixLift 7032153
  have htrace : WordTrace (prefixWord ++ tailWord_7032153) baseStart_7032153 baseEnd_7032153 := by
    simpa [prefixWord, tailWord_7032153, baseEnd_7032153] using wordTrace_append hprefix tailTrace_7032153
  have hstable : (prefixWord ++ tailWord_7032153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032153).length < 2 ^ (prefixWord ++ tailWord_7032153).sum := by decide
  have hdescent : baseEnd_7032153 < baseStart_7032153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032181 : List Nat := [1, 3, 4, 1, 4, 1, 2, 2, 1, 4]
def baseStart_7032181 : Nat := 118140960795 + 7032181 * 2 ^ 59
def prefixEnd_7032181 : Nat := 4983230072969 + 3 ^ 40 * 7032181 * 2
def baseEnd_7032181 : Nat := 1203629634138352097732365

theorem tailTrace_7032181 : CollatzResearch.WordTrace tailWord_7032181 prefixEnd_7032181 1203629634138352097732365 := by
  unfold tailWord_7032181
  simp only [CollatzResearch.WordTrace]
  refine ⟨256484712136616712743344397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170989808091077808495562931 256484712136616712743344397)
  ·
    refine ⟨96181767051231267278754149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256484712136616712743344397 96181767051231267278754149)
    ·
      refine ⟨18034081322105862614766403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96181767051231267278754149 18034081322105862614766403)
      ·
        refine ⟨27051121983158793922149605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18034081322105862614766403 27051121983158793922149605)
        ·
          refine ⟨5072085371842273860403051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27051121983158793922149605 5072085371842273860403051)
          ·
            refine ⟨7608128057763410790604577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5072085371842273860403051 7608128057763410790604577)
            ·
              refine ⟨5706096043322558092953433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7608128057763410790604577 5706096043322558092953433)
              ·
                refine ⟨4279572032491918569715075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5706096043322558092953433 4279572032491918569715075)
                ·
                  refine ⟨6419358048737877854572613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4279572032491918569715075 6419358048737877854572613)
                  ·
                    refine ⟨1203629634138352097732365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6419358048737877854572613 1203629634138352097732365)
                    ·
                      rfl

theorem cell23_7032181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_7032181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032181 prefixEnd_7032181 := by exact prefixLift 7032181
  have htrace : WordTrace (prefixWord ++ tailWord_7032181) baseStart_7032181 baseEnd_7032181 := by
    simpa [prefixWord, tailWord_7032181, baseEnd_7032181] using wordTrace_append hprefix tailTrace_7032181
  have hstable : (prefixWord ++ tailWord_7032181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032181).length < 2 ^ (prefixWord ++ tailWord_7032181).sum := by decide
  have hdescent : baseEnd_7032181 < baseStart_7032181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032203 : List Nat := [1, 1, 1, 1, 4, 3, 1, 5, 2, 4]
def baseStart_7032203 : Nat := 118140960795 + 7032203 * 2 ^ 59
def prefixEnd_7032203 : Nat := 4983230072969 + 3 ^ 40 * 7032203 * 2
def baseEnd_7032203 : Nat := 1203633399663151735707331

theorem tailTrace_7032203 : CollatzResearch.WordTrace tailWord_7032203 prefixEnd_7032203 1203633399663151735707331 := by
  unfold tailWord_7032203
  simp only [CollatzResearch.WordTrace]
  refine ⟨256485514542537010500645263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170990343028358007000430175 256485514542537010500645263)
  ·
    refine ⟨384728271813805515750967895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256485514542537010500645263 384728271813805515750967895)
    ·
      refine ⟨577092407720708273626451843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384728271813805515750967895 577092407720708273626451843)
      ·
        refine ⟨865638611581062410439677765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577092407720708273626451843 865638611581062410439677765)
        ·
          refine ⟨162307239671449201957439581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 865638611581062410439677765 162307239671449201957439581)
          ·
            refine ⟨60865214876793450734039843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162307239671449201957439581 60865214876793450734039843)
            ·
              refine ⟨91297822315190176101059765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60865214876793450734039843 91297822315190176101059765)
              ·
                refine ⟨8559170842049079009474353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91297822315190176101059765 8559170842049079009474353)
                ·
                  refine ⟨6419378131536809257105765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8559170842049079009474353 6419378131536809257105765)
                  ·
                    refine ⟨1203633399663151735707331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6419378131536809257105765 1203633399663151735707331)
                    ·
                      rfl

theorem cell23_7032203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 4].length) (baseStart_7032203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032203 prefixEnd_7032203 := by exact prefixLift 7032203
  have htrace : WordTrace (prefixWord ++ tailWord_7032203) baseStart_7032203 baseEnd_7032203 := by
    simpa [prefixWord, tailWord_7032203, baseEnd_7032203] using wordTrace_append hprefix tailTrace_7032203
  have hstable : (prefixWord ++ tailWord_7032203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032203).length < 2 ^ (prefixWord ++ tailWord_7032203).sum := by decide
  have hdescent : baseEnd_7032203 < baseStart_7032203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032213 : List Nat := [1, 3, 2, 1, 1, 2, 4, 1, 3, 2, 3]
def baseStart_7032213 : Nat := 118140960795 + 7032213 * 2 ^ 59
def prefixEnd_7032213 : Nat := 4983230072969 + 3 ^ 40 * 7032213 * 2
def baseEnd_7032213 : Nat := 3610905333796000167996947

theorem tailTrace_7032213 : CollatzResearch.WordTrace tailWord_7032213 prefixEnd_7032213 3610905333796000167996947 := by
  unfold tailWord_7032213
  simp only [CollatzResearch.WordTrace]
  refine ⟨256485879272500782208509293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170990586181667188139006195 256485879272500782208509293)
  ·
    refine ⟨96182204727187793328190985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256485879272500782208509293 96182204727187793328190985)
    ·
      refine ⟨72136653545390844996143239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96182204727187793328190985 72136653545390844996143239)
      ·
        refine ⟨108204980318086267494214859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72136653545390844996143239 108204980318086267494214859)
        ·
          refine ⟨162307470477129401241322289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108204980318086267494214859 162307470477129401241322289)
          ·
            refine ⟨121730602857847050930991717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162307470477129401241322289 121730602857847050930991717)
            ·
              refine ⟨22824488035846322049560947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121730602857847050930991717 22824488035846322049560947)
              ·
                refine ⟨34236732053769483074341421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22824488035846322049560947 34236732053769483074341421)
                ·
                  refine ⟨12838774520163556152878033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34236732053769483074341421 12838774520163556152878033)
                  ·
                    refine ⟨9629080890122667114658525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12838774520163556152878033 9629080890122667114658525)
                    ·
                      refine ⟨3610905333796000167996947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9629080890122667114658525 3610905333796000167996947)
                      ·
                        rfl

theorem cell23_7032213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_7032213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032213 prefixEnd_7032213 := by exact prefixLift 7032213
  have htrace : WordTrace (prefixWord ++ tailWord_7032213) baseStart_7032213 baseEnd_7032213 := by
    simpa [prefixWord, tailWord_7032213, baseEnd_7032213] using wordTrace_append hprefix tailTrace_7032213
  have hstable : (prefixWord ++ tailWord_7032213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032213).length < 2 ^ (prefixWord ++ tailWord_7032213).sum := by decide
  have hdescent : baseEnd_7032213 < baseStart_7032213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032223 : List Nat := [1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 4]
def baseStart_7032223 : Nat := 118140960795 + 7032223 * 2 ^ 59
def prefixEnd_7032223 : Nat := 4983230072969 + 3 ^ 40 * 7032223 * 2
def baseEnd_7032223 : Nat := 3610910468602545128871901

theorem tailTrace_7032223 : CollatzResearch.WordTrace tailWord_7032223 prefixEnd_7032223 3610910468602545128871901 := by
  unfold tailWord_7032223
  simp only [CollatzResearch.WordTrace]
  refine ⟨256486244002464553916373323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170990829334976369277582215 256486244002464553916373323)
  ·
    refine ⟨384729366003696830874559985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256486244002464553916373323 384729366003696830874559985)
    ·
      refine ⟨288547024502772623155919989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384729366003696830874559985 288547024502772623155919989)
      ·
        refine ⟨27051283547134933420867499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 288547024502772623155919989 27051283547134933420867499)
        ·
          refine ⟨40576925320702400131301249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27051283547134933420867499 40576925320702400131301249)
          ·
            refine ⟨30432693990526800098475937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40576925320702400131301249 30432693990526800098475937)
            ·
              refine ⟨22824520492895100073856953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30432693990526800098475937 22824520492895100073856953)
              ·
                refine ⟨17118390369671325055392715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22824520492895100073856953 17118390369671325055392715)
                ·
                  refine ⟨25677585554506987583089073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17118390369671325055392715 25677585554506987583089073)
                  ·
                    refine ⟨19258189165880240687316805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25677585554506987583089073 19258189165880240687316805)
                    ·
                      refine ⟨3610910468602545128871901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19258189165880240687316805 3610910468602545128871901)
                      ·
                        rfl

theorem cell23_7032223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_7032223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032223 prefixEnd_7032223 := by exact prefixLift 7032223
  have htrace : WordTrace (prefixWord ++ tailWord_7032223) baseStart_7032223 baseEnd_7032223 := by
    simpa [prefixWord, tailWord_7032223, baseEnd_7032223] using wordTrace_append hprefix tailTrace_7032223
  have hstable : (prefixWord ++ tailWord_7032223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032223).length < 2 ^ (prefixWord ++ tailWord_7032223).sum := by decide
  have hdescent : baseEnd_7032223 < baseStart_7032223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032237 : List Nat := [1, 5, 2, 2, 1, 1, 3, 2, 2, 4]
def baseStart_7032237 : Nat := 118140960795 + 7032237 * 2 ^ 59
def prefixEnd_7032237 : Nat := 4983230072969 + 3 ^ 40 * 7032237 * 2
def baseEnd_7032237 : Nat := 1203639219110569358032279

theorem tailTrace_7032237 : CollatzResearch.WordTrace tailWord_7032237 prefixEnd_7032237 1203639219110569358032279 := by
  unfold tailWord_7032237
  simp only [CollatzResearch.WordTrace]
  refine ⟨256486754624413834307382965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170991169749609222871588643 256486754624413834307382965)
  ·
    refine ⟨24045633246038796966317153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 256486754624413834307382965 24045633246038796966317153)
    ·
      refine ⟨18034224934529097724737865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24045633246038796966317153 18034224934529097724737865)
      ·
        refine ⟨13525668700896823293553399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18034224934529097724737865 13525668700896823293553399)
        ·
          refine ⟨20288503051345234940330099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13525668700896823293553399 20288503051345234940330099)
          ·
            refine ⟨30432754577017852410495149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20288503051345234940330099 30432754577017852410495149)
            ·
              refine ⟨11412282966381694653935681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30432754577017852410495149 11412282966381694653935681)
              ·
                refine ⟨8559212224786270990451761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11412282966381694653935681 8559212224786270990451761)
                ·
                  refine ⟨6419409168589703242838821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8559212224786270990451761 6419409168589703242838821)
                  ·
                    refine ⟨1203639219110569358032279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6419409168589703242838821 1203639219110569358032279)
                    ·
                      rfl

theorem cell23_7032237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_7032237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032237 prefixEnd_7032237 := by exact prefixLift 7032237
  have htrace : WordTrace (prefixWord ++ tailWord_7032237) baseStart_7032237 baseEnd_7032237 := by
    simpa [prefixWord, tailWord_7032237, baseEnd_7032237] using wordTrace_append hprefix tailTrace_7032237
  have hstable : (prefixWord ++ tailWord_7032237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032237).length < 2 ^ (prefixWord ++ tailWord_7032237).sum := by decide
  have hdescent : baseEnd_7032237 < baseStart_7032237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032270 : List Nat := [4, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2]
def baseStart_7032270 : Nat := 118140960795 + 7032270 * 2 ^ 59
def prefixEnd_7032270 : Nat := 4983230072969 + 3 ^ 40 * 7032270 * 2
def baseEnd_7032270 : Nat := 3610934602193306444984185

theorem tailTrace_7032270 : CollatzResearch.WordTrace tailWord_7032270 prefixEnd_7032270 3610934602193306444984185 := by
  unfold tailWord_7032270
  simp only [CollatzResearch.WordTrace]
  refine ⟨32060994779161785117916783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170991972155529520628889509 32060994779161785117916783)
  ·
    refine ⟨48091492168742677676875175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32060994779161785117916783 48091492168742677676875175)
    ·
      refine ⟨72137238253114016515312763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48091492168742677676875175 72137238253114016515312763)
      ·
        refine ⟨108205857379671024772969145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72137238253114016515312763 108205857379671024772969145)
        ·
          refine ⟨81154393034753268579726859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108205857379671024772969145 81154393034753268579726859)
          ·
            refine ⟨121731589552129902869590289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81154393034753268579726859 121731589552129902869590289)
            ·
              refine ⟨91298692164097427152192717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121731589552129902869590289 91298692164097427152192717)
              ·
                refine ⟨34237009561536535182072269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91298692164097427152192717 34237009561536535182072269)
                ·
                  refine ⟨12838878585576200693277101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34237009561536535182072269 12838878585576200693277101)
                  ·
                    refine ⟨4814579469591075259978913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12838878585576200693277101 4814579469591075259978913)
                    ·
                      refine ⟨3610934602193306444984185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4814579469591075259978913 3610934602193306444984185)
                      ·
                        rfl

theorem cell23_7032270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2].length) (baseStart_7032270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032270 prefixEnd_7032270 := by exact prefixLift 7032270
  have htrace : WordTrace (prefixWord ++ tailWord_7032270) baseStart_7032270 baseEnd_7032270 := by
    simpa [prefixWord, tailWord_7032270, baseEnd_7032270] using wordTrace_append hprefix tailTrace_7032270
  have hstable : (prefixWord ++ tailWord_7032270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032270).length < 2 ^ (prefixWord ++ tailWord_7032270).sum := by decide
  have hdescent : baseEnd_7032270 < baseStart_7032270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032278 : List Nat := [5, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2]
def baseStart_7032278 : Nat := 118140960795 + 7032278 * 2 ^ 59
def prefixEnd_7032278 : Nat := 4983230072969 + 3 ^ 40 * 7032278 * 2
def baseEnd_7032278 : Nat := 3610938710038542413684149

theorem tailTrace_7032278 : CollatzResearch.WordTrace tailWord_7032278 prefixEnd_7032278 3610938710038542413684149 := by
  unfold tailWord_7032278
  simp only [CollatzResearch.WordTrace]
  refine ⟨16030515626079081144351593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170992166678176865539750325 16030515626079081144351593)
  ·
    refine ⟨12022886719559310858263695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16030515626079081144351593 12022886719559310858263695)
    ·
      refine ⟨18034330079338966287395543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12022886719559310858263695 18034330079338966287395543)
      ·
        refine ⟨27051495119008449431093315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18034330079338966287395543 27051495119008449431093315)
        ·
          refine ⟨40577242678512674146639973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27051495119008449431093315 40577242678512674146639973)
          ·
            refine ⟨7608233002221126402494995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40577242678512674146639973 7608233002221126402494995)
            ·
              refine ⟨11412349503331689603742493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7608233002221126402494995 11412349503331689603742493)
              ·
                refine ⟨4279631063749383601403435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11412349503331689603742493 4279631063749383601403435)
                ·
                  refine ⟨6419446595624075402105153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4279631063749383601403435 6419446595624075402105153)
                  ·
                    refine ⟨4814584946718056551578865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6419446595624075402105153 4814584946718056551578865)
                    ·
                      refine ⟨3610938710038542413684149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4814584946718056551578865 3610938710038542413684149)
                      ·
                        rfl

theorem cell23_7032278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_7032278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032278 prefixEnd_7032278 := by exact prefixLift 7032278
  have htrace : WordTrace (prefixWord ++ tailWord_7032278) baseStart_7032278 baseEnd_7032278 := by
    simpa [prefixWord, tailWord_7032278, baseEnd_7032278] using wordTrace_append hprefix tailTrace_7032278
  have hstable : (prefixWord ++ tailWord_7032278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032278).length < 2 ^ (prefixWord ++ tailWord_7032278).sum := by decide
  have hdescent : baseEnd_7032278 < baseStart_7032278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032321 : List Nat := [1, 2, 4, 1, 5, 1, 1, 2, 1, 3, 2]
def baseStart_7032321 : Nat := 118140960795 + 7032321 * 2 ^ 59
def prefixEnd_7032321 : Nat := 4983230072969 + 3 ^ 40 * 7032321 * 2
def baseEnd_7032321 : Nat := 3610960789706685745446451

theorem tailTrace_7032321 : CollatzResearch.WordTrace tailWord_7032321 prefixEnd_7032321 3610960789706685745446451 := by
  unfold tailWord_7032321
  simp only [CollatzResearch.WordTrace]
  refine ⟨256489818356109516653440817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170993212237406344435627211 256489818356109516653440817)
  ·
    refine ⟨192367363767082137490080613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256489818356109516653440817 192367363767082137490080613)
    ·
      refine ⟨36068880706327900779390115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192367363767082137490080613 36068880706327900779390115)
      ·
        refine ⟨54103321059491851169085173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36068880706327900779390115 54103321059491851169085173)
        ·
          refine ⟨5072186349327361047101735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54103321059491851169085173 5072186349327361047101735)
          ·
            refine ⟨7608279523991041570652603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5072186349327361047101735 7608279523991041570652603)
            ·
              refine ⟨11412419285986562355978905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7608279523991041570652603 11412419285986562355978905)
              ·
                refine ⟨8559314464489921766984179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11412419285986562355978905 8559314464489921766984179)
                ·
                  refine ⟨12838971696734882650476269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8559314464489921766984179 12838971696734882650476269)
                  ·
                    refine ⟨4814614386275580993928601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12838971696734882650476269 4814614386275580993928601)
                    ·
                      refine ⟨3610960789706685745446451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4814614386275580993928601 3610960789706685745446451)
                      ·
                        rfl

theorem cell23_7032321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_7032321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032321 prefixEnd_7032321 := by exact prefixLift 7032321
  have htrace : WordTrace (prefixWord ++ tailWord_7032321) baseStart_7032321 baseEnd_7032321 := by
    simpa [prefixWord, tailWord_7032321, baseEnd_7032321] using wordTrace_append hprefix tailTrace_7032321
  have hstable : (prefixWord ++ tailWord_7032321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032321).length < 2 ^ (prefixWord ++ tailWord_7032321).sum := by decide
  have hdescent : baseEnd_7032321 < baseStart_7032321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032410 : List Nat := [3, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3]
def baseStart_7032410 : Nat := 118140960795 + 7032410 * 2 ^ 59
def prefixEnd_7032410 : Nat := 4983230072969 + 3 ^ 40 * 7032410 * 2
def baseEnd_7032410 : Nat := 3611006489484935897233541

theorem tailTrace_7032410 : CollatzResearch.WordTrace tailWord_7032410 prefixEnd_7032410 3611006489484935897233541 := by
  unfold tailWord_7032410
  simp only [CollatzResearch.WordTrace]
  refine ⟨64123266113196771213357671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170995376301858056568953789 64123266113196771213357671)
  ·
    refine ⟨96184899169795156820036507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64123266113196771213357671 96184899169795156820036507)
    ·
      refine ⟨144277348754692735230054761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96184899169795156820036507 144277348754692735230054761)
      ·
        refine ⟨108208011566019551422541071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144277348754692735230054761 108208011566019551422541071)
        ·
          refine ⟨162312017349029327133811607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108208011566019551422541071 162312017349029327133811607)
          ·
            refine ⟨243468026023543990700717411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162312017349029327133811607 243468026023543990700717411)
            ·
              refine ⟨365202039035315986051076117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243468026023543990700717411 365202039035315986051076117)
              ·
                refine ⟨17118845579780436846144193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 365202039035315986051076117 17118845579780436846144193)
                ·
                  refine ⟨12839134184835327634608145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17118845579780436846144193 12839134184835327634608145)
                  ·
                    refine ⟨9629350638626495725956109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12839134184835327634608145 9629350638626495725956109)
                    ·
                      refine ⟨3611006489484935897233541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9629350638626495725956109 3611006489484935897233541)
                      ·
                        rfl

theorem cell23_7032410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_7032410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032410 prefixEnd_7032410 := by exact prefixLift 7032410
  have htrace : WordTrace (prefixWord ++ tailWord_7032410) baseStart_7032410 baseEnd_7032410 := by
    simpa [prefixWord, tailWord_7032410, baseEnd_7032410] using wordTrace_append hprefix tailTrace_7032410
  have hstable : (prefixWord ++ tailWord_7032410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032410).length < 2 ^ (prefixWord ++ tailWord_7032410).sum := by decide
  have hdescent : baseEnd_7032410 < baseStart_7032410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032417 : List Nat := [1, 2, 3, 1, 1, 3, 1, 6, 1, 4]
def baseStart_7032417 : Nat := 118140960795 + 7032417 * 2 ^ 59
def prefixEnd_7032417 : Nat := 4983230072969 + 3 ^ 40 * 7032417 * 2
def baseEnd_7032417 : Nat := 1203670027949839123282003

theorem tailTrace_7032417 : CollatzResearch.WordTrace tailWord_7032417 prefixEnd_7032417 1203670027949839123282003 := by
  unfold tailWord_7032417
  simp only [CollatzResearch.WordTrace]
  refine ⟨256493319763761725048935505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170995546509174483365957003 256493319763761725048935505)
  ·
    refine ⟨192369989822821293786701629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256493319763761725048935505 192369989822821293786701629)
    ·
      refine ⟨72138746183557985170013111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192369989822821293786701629 72138746183557985170013111)
      ·
        refine ⟨108208119275336977755019667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72138746183557985170013111 108208119275336977755019667)
        ·
          refine ⟨162312178913005466632529501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108208119275336977755019667 162312178913005466632529501)
          ·
            refine ⟨60867067092377049987198563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162312178913005466632529501 60867067092377049987198563)
            ·
              refine ⟨91300600638565574980797845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60867067092377049987198563 91300600638565574980797845)
              ·
                refine ⟨4279715654932761327224899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91300600638565574980797845 4279715654932761327224899)
                ·
                  refine ⟨6419573482399141990837349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4279715654932761327224899 6419573482399141990837349)
                  ·
                    refine ⟨1203670027949839123282003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6419573482399141990837349 1203670027949839123282003)
                    ·
                      rfl

theorem cell23_7032417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_7032417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032417 prefixEnd_7032417 := by exact prefixLift 7032417
  have htrace : WordTrace (prefixWord ++ tailWord_7032417) baseStart_7032417 baseEnd_7032417 := by
    simpa [prefixWord, tailWord_7032417, baseEnd_7032417] using wordTrace_append hprefix tailTrace_7032417
  have hstable : (prefixWord ++ tailWord_7032417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032417).length < 2 ^ (prefixWord ++ tailWord_7032417).sum := by decide
  have hdescent : baseEnd_7032417 < baseStart_7032417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032460 : List Nat := [2, 2, 1, 2, 1, 1, 3, 5, 1, 5]
def baseStart_7032460 : Nat := 118140960795 + 7032460 * 2 ^ 59
def prefixEnd_7032460 : Nat := 4983230072969 + 3 ^ 40 * 7032460 * 2
def baseEnd_7032460 : Nat := 1203677387839220233869437

theorem tailTrace_7032460 : CollatzResearch.WordTrace tailWord_7032460 prefixEnd_7032460 1203677387839220233869437 := by
  unfold tailWord_7032460
  simp only [CollatzResearch.WordTrace]
  refine ⟨128247444051302971696375417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170996592068403962261833889 128247444051302971696375417)
  ·
    refine ⟨96185583038477228772281563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128247444051302971696375417 96185583038477228772281563)
    ·
      refine ⟨144278374557715843158422345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96185583038477228772281563 144278374557715843158422345)
      ·
        refine ⟨108208780918286882368816759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144278374557715843158422345 108208780918286882368816759)
        ·
          refine ⟨162313171377430323553225139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108208780918286882368816759 162313171377430323553225139)
          ·
            refine ⟨243469757066145485329837709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162313171377430323553225139 243469757066145485329837709)
            ·
              refine ⟨91301158899804556998689141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243469757066145485329837709 91301158899804556998689141)
              ·
                refine ⟨8559483646856677218627107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91301158899804556998689141 8559483646856677218627107)
                ·
                  refine ⟨12839225470285015827940661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8559483646856677218627107 12839225470285015827940661)
                  ·
                    refine ⟨1203677387839220233869437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12839225470285015827940661 1203677387839220233869437)
                    ·
                      rfl

theorem cell23_7032460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 1, 5].length) (baseStart_7032460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032460 prefixEnd_7032460 := by exact prefixLift 7032460
  have htrace : WordTrace (prefixWord ++ tailWord_7032460) baseStart_7032460 baseEnd_7032460 := by
    simpa [prefixWord, tailWord_7032460, baseEnd_7032460] using wordTrace_append hprefix tailTrace_7032460
  have hstable : (prefixWord ++ tailWord_7032460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032460).length < 2 ^ (prefixWord ++ tailWord_7032460).sum := by decide
  have hdescent : baseEnd_7032460 < baseStart_7032460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032468 : List Nat := [2, 4, 2, 2, 2, 1, 3, 2, 1, 4]
def baseStart_7032468 : Nat := 118140960795 + 7032468 * 2 ^ 59
def prefixEnd_7032468 : Nat := 4983230072969 + 3 ^ 40 * 7032468 * 2
def baseEnd_7032468 : Nat := 1203678757120965556769425

theorem tailTrace_7032468 : CollatzResearch.WordTrace tailWord_7032468 prefixEnd_7032468 1203678757120965556769425 := by
  unfold tailWord_7032468
  simp only [CollatzResearch.WordTrace]
  refine ⟨128247589943288480379521029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170996786591051307172694705 128247589943288480379521029)
  ·
    refine ⟨24046423114366590071160193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128247589943288480379521029 24046423114366590071160193)
    ·
      refine ⟨18034817335774942553370145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24046423114366590071160193 18034817335774942553370145)
      ·
        refine ⟨13526113001831206915027609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18034817335774942553370145 13526113001831206915027609)
        ·
          refine ⟨10144584751373405186270707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13526113001831206915027609 10144584751373405186270707)
          ·
            refine ⟨15216877127060107779406061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10144584751373405186270707 15216877127060107779406061)
            ·
              refine ⟨5706328922647540417277273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15216877127060107779406061 5706328922647540417277273)
              ·
                refine ⟨4279746691985655312957955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5706328922647540417277273 4279746691985655312957955)
                ·
                  refine ⟨6419620037978482969436933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4279746691985655312957955 6419620037978482969436933)
                  ·
                    refine ⟨1203678757120965556769425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6419620037978482969436933 1203678757120965556769425)
                    ·
                      rfl

theorem cell23_7032468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_7032468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032468 prefixEnd_7032468 := by exact prefixLift 7032468
  have htrace : WordTrace (prefixWord ++ tailWord_7032468) baseStart_7032468 baseEnd_7032468 := by
    simpa [prefixWord, tailWord_7032468, baseEnd_7032468] using wordTrace_append hprefix tailTrace_7032468
  have hstable : (prefixWord ++ tailWord_7032468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032468).length < 2 ^ (prefixWord ++ tailWord_7032468).sum := by decide
  have hdescent : baseEnd_7032468 < baseStart_7032468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032473 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 5, 6]
def baseStart_7032473 : Nat := 118140960795 + 7032473 * 2 ^ 59
def prefixEnd_7032473 : Nat := 4983230072969 + 3 ^ 40 * 7032473 * 2
def baseEnd_7032473 : Nat := 1203679612922056383581917

theorem tailTrace_7032473 : CollatzResearch.WordTrace tailWord_7032473 prefixEnd_7032473 1203679612922056383581917 := by
  unfold tailWord_7032473
  simp only [CollatzResearch.WordTrace]
  refine ⟨256495362251558846612974073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170996908167705897741982715 256495362251558846612974073)
  ·
    refine ⟨192371521688669134959730555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256495362251558846612974073 192371521688669134959730555)
    ·
      refine ⟨288557282533003702439595833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192371521688669134959730555 288557282533003702439595833)
      ·
        refine ⟨216417961899752776829696875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288557282533003702439595833 216417961899752776829696875)
        ·
          refine ⟨324626942849629165244545313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216417961899752776829696875 324626942849629165244545313)
          ·
            refine ⟨243470207137221873933408985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324626942849629165244545313 243470207137221873933408985)
            ·
              refine ⟨182602655352916405450056739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243470207137221873933408985 182602655352916405450056739)
              ·
                refine ⟨273903983029374608175085109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182602655352916405450056739 273903983029374608175085109)
                ·
                  refine ⟨25678498409003869516414229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 273903983029374608175085109 25678498409003869516414229)
                  ·
                    refine ⟨1203679612922056383581917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25678498409003869516414229 1203679612922056383581917)
                    ·
                      rfl

theorem cell23_7032473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 6].length) (baseStart_7032473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032473 prefixEnd_7032473 := by exact prefixLift 7032473
  have htrace : WordTrace (prefixWord ++ tailWord_7032473) baseStart_7032473 baseEnd_7032473 := by
    simpa [prefixWord, tailWord_7032473, baseEnd_7032473] using wordTrace_append hprefix tailTrace_7032473
  have hstable : (prefixWord ++ tailWord_7032473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032473).length < 2 ^ (prefixWord ++ tailWord_7032473).sum := by decide
  have hdescent : baseEnd_7032473 < baseStart_7032473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032494 : List Nat := [4, 1, 4, 1, 2, 1, 1, 1, 3, 5]
def baseStart_7032494 : Nat := 118140960795 + 7032494 * 2 ^ 59
def prefixEnd_7032494 : Nat := 4983230072969 + 3 ^ 40 * 7032494 * 2
def baseEnd_7032494 : Nat := 1203683207286637856194385

theorem tailTrace_7032494 : CollatzResearch.WordTrace tailWord_7032494 prefixEnd_7032494 1203683207286637856194385 := by
  unfold tailWord_7032494
  simp only [CollatzResearch.WordTrace]
  refine ⟨32062016023060345899936067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170997418789655178132992357 32062016023060345899936067)
  ·
    refine ⟨48093024034590518849904101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32062016023060345899936067 48093024034590518849904101)
    ·
      refine ⟨9017442006485722284357019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48093024034590518849904101 9017442006485722284357019)
      ·
        refine ⟨13526163009728583426535529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9017442006485722284357019 13526163009728583426535529)
        ·
          refine ⟨10144622257296437569901647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13526163009728583426535529 10144622257296437569901647)
          ·
            refine ⟨15216933385944656354852471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10144622257296437569901647 15216933385944656354852471)
            ·
              refine ⟨22825400078916984532278707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15216933385944656354852471 22825400078916984532278707)
              ·
                refine ⟨34238100118375476798418061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22825400078916984532278707 34238100118375476798418061)
                ·
                  refine ⟨12839287544390803799406773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34238100118375476798418061 12839287544390803799406773)
                  ·
                    refine ⟨1203683207286637856194385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12839287544390803799406773 1203683207286637856194385)
                    ·
                      rfl

theorem cell23_7032494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_7032494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032494 prefixEnd_7032494 := by exact prefixLift 7032494
  have htrace : WordTrace (prefixWord ++ tailWord_7032494) baseStart_7032494 baseEnd_7032494 := by
    simpa [prefixWord, tailWord_7032494, baseEnd_7032494] using wordTrace_append hprefix tailTrace_7032494
  have hstable : (prefixWord ++ tailWord_7032494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032494).length < 2 ^ (prefixWord ++ tailWord_7032494).sum := by decide
  have hdescent : baseEnd_7032494 < baseStart_7032494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032501 : List Nat := [1, 3, 3, 3, 2, 1, 2, 1, 2, 3, 2]
def baseStart_7032501 : Nat := 118140960795 + 7032501 * 2 ^ 59
def prefixEnd_7032501 : Nat := 4983230072969 + 3 ^ 40 * 7032501 * 2
def baseEnd_7032501 : Nat := 3611053216224495041195623

theorem tailTrace_7032501 : CollatzResearch.WordTrace tailWord_7032501 prefixEnd_7032501 3611053216224495041195623 := by
  unfold tailWord_7032501
  simp only [CollatzResearch.WordTrace]
  refine ⟨256496383495457407394993357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170997588996971604929995571 256496383495457407394993357)
  ·
    refine ⟨96186143810796527773122509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256496383495457407394993357 96186143810796527773122509)
    ·
      refine ⟨36069803929048697914920941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96186143810796527773122509 36069803929048697914920941)
      ·
        refine ⟨13526176473393261718095353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36069803929048697914920941 13526176473393261718095353)
        ·
          refine ⟨10144632355044946288571515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13526176473393261718095353 10144632355044946288571515)
          ·
            refine ⟨15216948532567419432857273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10144632355044946288571515 15216948532567419432857273)
            ·
              refine ⟨11412711399425564574642955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15216948532567419432857273 11412711399425564574642955)
              ·
                refine ⟨17119067099138346861964433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11412711399425564574642955 17119067099138346861964433)
                ·
                  refine ⟨12839300324353760146473325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17119067099138346861964433 12839300324353760146473325)
                  ·
                    refine ⟨4814737621632660054927497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12839300324353760146473325 4814737621632660054927497)
                    ·
                      refine ⟨3611053216224495041195623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4814737621632660054927497 3611053216224495041195623)
                      ·
                        rfl

theorem cell23_7032501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_7032501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032501 prefixEnd_7032501 := by exact prefixLift 7032501
  have htrace : WordTrace (prefixWord ++ tailWord_7032501) baseStart_7032501 baseEnd_7032501 := by
    simpa [prefixWord, tailWord_7032501, baseEnd_7032501] using wordTrace_append hprefix tailTrace_7032501
  have hstable : (prefixWord ++ tailWord_7032501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032501).length < 2 ^ (prefixWord ++ tailWord_7032501).sum := by decide
  have hdescent : baseEnd_7032501 < baseStart_7032501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032518 : List Nat := [6, 1, 2, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_7032518 : Nat := 118140960795 + 7032518 * 2 ^ 59
def prefixEnd_7032518 : Nat := 4983230072969 + 3 ^ 40 * 7032518 * 2
def baseEnd_7032518 : Nat := 3611061945395621474683045

theorem tailTrace_7032518 : CollatzResearch.WordTrace tailWord_7032518 prefixEnd_7032518 3611061945395621474683045 := by
  unfold tailWord_7032518
  simp only [CollatzResearch.WordTrace]
  refine ⟨8015531360512369353073819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 170998002357597212865574805 8015531360512369353073819)
  ·
    refine ⟨12023297040768554029610729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8015531360512369353073819 12023297040768554029610729)
    ·
      refine ⟨9017472780576415522208047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12023297040768554029610729 9017472780576415522208047)
      ·
        refine ⟨13526209170864623283312071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9017472780576415522208047 13526209170864623283312071)
        ·
          refine ⟨20289313756296934924968107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13526209170864623283312071 20289313756296934924968107)
          ·
            refine ⟨30433970634445402387452161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20289313756296934924968107 30433970634445402387452161)
            ·
              refine ⟨22825477975834051790589121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30433970634445402387452161 22825477975834051790589121)
              ·
                refine ⟨17119108481875538842941841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22825477975834051790589121 17119108481875538842941841)
                ·
                  refine ⟨12839331361406654132206381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17119108481875538842941841 12839331361406654132206381)
                  ·
                    refine ⟨4814749260527495299577393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12839331361406654132206381 4814749260527495299577393)
                    ·
                      refine ⟨3611061945395621474683045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4814749260527495299577393 3611061945395621474683045)
                      ·
                        rfl

theorem cell23_7032518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_7032518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032518 prefixEnd_7032518 := by exact prefixLift 7032518
  have htrace : WordTrace (prefixWord ++ tailWord_7032518) baseStart_7032518 baseEnd_7032518 := by
    simpa [prefixWord, tailWord_7032518, baseEnd_7032518] using wordTrace_append hprefix tailTrace_7032518
  have hstable : (prefixWord ++ tailWord_7032518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032518).length < 2 ^ (prefixWord ++ tailWord_7032518).sum := by decide
  have hdescent : baseEnd_7032518 < baseStart_7032518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032525 : List Nat := [1, 6, 2, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_7032525 : Nat := 118140960795 + 7032525 * 2 ^ 59
def prefixEnd_7032525 : Nat := 4983230072969 + 3 ^ 40 * 7032525 * 2
def baseEnd_7032525 : Nat := 3611065539760202947295513

theorem tailTrace_7032525 : CollatzResearch.WordTrace tailWord_7032525 prefixEnd_7032525 3611065539760202947295513 := by
  unfold tailWord_7032525
  simp only [CollatzResearch.WordTrace]
  refine ⟨256497258847370459493867029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170998172564913639662578019 256497258847370459493867029)
  ·
    refine ⟨12023309008470490288775017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 256497258847370459493867029 12023309008470490288775017)
    ·
      refine ⟨9017481756352867716581263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12023309008470490288775017 9017481756352867716581263)
      ·
        refine ⟨13526222634529301574871895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9017481756352867716581263 13526222634529301574871895)
        ·
          refine ⟨20289333951793952362307843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13526222634529301574871895 20289333951793952362307843)
          ·
            refine ⟨30434000927690928543461765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20289333951793952362307843 30434000927690928543461765)
            ·
              refine ⟨5706375173942049101899081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30434000927690928543461765 5706375173942049101899081)
              ·
                refine ⟨4279781380456536826424311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5706375173942049101899081 4279781380456536826424311)
                ·
                  refine ⟨6419672070684805239636467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4279781380456536826424311 6419672070684805239636467)
                  ·
                    refine ⟨9629508106027207859454701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6419672070684805239636467 9629508106027207859454701)
                    ·
                      refine ⟨3611065539760202947295513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9629508106027207859454701 3611065539760202947295513)
                      ·
                        rfl

theorem cell23_7032525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_7032525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032525 prefixEnd_7032525 := by exact prefixLift 7032525
  have htrace : WordTrace (prefixWord ++ tailWord_7032525) baseStart_7032525 baseEnd_7032525 := by
    simpa [prefixWord, tailWord_7032525, baseEnd_7032525] using wordTrace_append hprefix tailTrace_7032525
  have hstable : (prefixWord ++ tailWord_7032525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032525).length < 2 ^ (prefixWord ++ tailWord_7032525).sum := by decide
  have hdescent : baseEnd_7032525 < baseStart_7032525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032587 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 3, 4, 2]
def baseStart_7032587 : Nat := 118140960795 + 7032587 * 2 ^ 59
def prefixEnd_7032587 : Nat := 4983230072969 + 3 ^ 40 * 7032587 * 2
def baseEnd_7032587 : Nat := 3611097375560781704720227

theorem tailTrace_7032587 : CollatzResearch.WordTrace tailWord_7032587 prefixEnd_7032587 3611097375560781704720227 := by
  unfold tailWord_7032587
  simp only [CollatzResearch.WordTrace]
  refine ⟨256499520173145844082624015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170999680115430562721749343 256499520173145844082624015)
  ·
    refine ⟨384749280259718766123936023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256499520173145844082624015 384749280259718766123936023)
    ·
      refine ⟨577123920389578149185904035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384749280259718766123936023 577123920389578149185904035)
      ·
        refine ⟨865685880584367223778856053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577123920389578149185904035 865685880584367223778856053)
        ·
          refine ⟨81158051304784427229267755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 865685880584367223778856053 81158051304784427229267755)
          ·
            refine ⟨121737076957176640843901633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81158051304784427229267755 121737076957176640843901633)
            ·
              refine ⟨91302807717882480632926225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121737076957176640843901633 91302807717882480632926225)
              ·
                refine ⟨68477105788411860474694669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91302807717882480632926225 68477105788411860474694669)
                ·
                  refine ⟨25678914670654447678010501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68477105788411860474694669 25678914670654447678010501)
                  ·
                    refine ⟨4814796500747708939626969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25678914670654447678010501 4814796500747708939626969)
                    ·
                      refine ⟨3611097375560781704720227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4814796500747708939626969 3611097375560781704720227)
                      ·
                        rfl

theorem cell23_7032587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 4, 2].length) (baseStart_7032587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032587 prefixEnd_7032587 := by exact prefixLift 7032587
  have htrace : WordTrace (prefixWord ++ tailWord_7032587) baseStart_7032587 baseEnd_7032587 := by
    simpa [prefixWord, tailWord_7032587, baseEnd_7032587] using wordTrace_append hprefix tailTrace_7032587
  have hstable : (prefixWord ++ tailWord_7032587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032587).length < 2 ^ (prefixWord ++ tailWord_7032587).sum := by decide
  have hdescent : baseEnd_7032587 < baseStart_7032587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032674 : List Nat := [3, 3, 2, 1, 2, 1, 1, 3, 2, 5]
def baseStart_7032674 : Nat := 118140960795 + 7032674 * 2 ^ 59
def prefixEnd_7032674 : Nat := 4983230072969 + 3 ^ 40 * 7032674 * 2
def baseEnd_7032674 : Nat := 1203714016125907621444109

theorem tailTrace_7032674 : CollatzResearch.WordTrace tailWord_7032674 prefixEnd_7032674 1203714016125907621444109 := by
  unfold tailWord_7032674
  simp only [CollatzResearch.WordTrace]
  refine ⟨64125673330957664485260269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171001795549220438627360717 64125673330957664485260269)
  ·
    refine ⟨24047127499109124181972601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64125673330957664485260269 24047127499109124181972601)
    ·
      refine ⟨18035345624331843136479451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24047127499109124181972601 18035345624331843136479451)
      ·
        refine ⟨27053018436497764704719177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18035345624331843136479451 27053018436497764704719177)
        ·
          refine ⟨20289763827373323528539383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27053018436497764704719177 20289763827373323528539383)
          ·
            refine ⟨30434645741059985292809075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20289763827373323528539383 30434645741059985292809075)
            ·
              refine ⟨45651968611589977939213613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30434645741059985292809075 45651968611589977939213613)
              ·
                refine ⟨17119488229346241727205105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45651968611589977939213613 17119488229346241727205105)
                ·
                  refine ⟨12839616172009681295403829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17119488229346241727205105 12839616172009681295403829)
                  ·
                    refine ⟨1203714016125907621444109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12839616172009681295403829 1203714016125907621444109)
                    ·
                      rfl

theorem cell23_7032674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_7032674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032674 prefixEnd_7032674 := by exact prefixLift 7032674
  have htrace : WordTrace (prefixWord ++ tailWord_7032674) baseStart_7032674 baseEnd_7032674 := by
    simpa [prefixWord, tailWord_7032674, baseEnd_7032674] using wordTrace_append hprefix tailTrace_7032674
  have hstable : (prefixWord ++ tailWord_7032674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032674).length < 2 ^ (prefixWord ++ tailWord_7032674).sum := by decide
  have hdescent : baseEnd_7032674 < baseStart_7032674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032711 : List Nat := [1, 1, 4, 2, 4, 1, 1, 1, 2, 4, 2]
def baseStart_7032711 : Nat := 118140960795 + 7032711 * 2 ^ 59
def prefixEnd_7032711 : Nat := 4983230072969 + 3 ^ 40 * 7032711 * 2
def baseEnd_7032711 : Nat := 3611161047161939219569657

theorem tailTrace_7032711 : CollatzResearch.WordTrace tailWord_7032711 prefixEnd_7032711 3611161047161939219569657 := by
  unfold tailWord_7032711
  simp only [CollatzResearch.WordTrace]
  refine ⟨256504042824696613260137987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171002695216464408840091991 256504042824696613260137987)
  ·
    refine ⟨384756064237044919890206981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256504042824696613260137987 384756064237044919890206981)
    ·
      refine ⟨72141762044445922479413809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 384756064237044919890206981 72141762044445922479413809)
      ·
        refine ⟨54106321533334441859560357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72141762044445922479413809 54106321533334441859560357)
        ·
          refine ⟨10144935287500207848667567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54106321533334441859560357 10144935287500207848667567)
          ·
            refine ⟨15217402931250311773001351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10144935287500207848667567 15217402931250311773001351)
            ·
              refine ⟨22826104396875467659502027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15217402931250311773001351 22826104396875467659502027)
              ·
                refine ⟨34239156595313201489253041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22826104396875467659502027 34239156595313201489253041)
                ·
                  refine ⟨25679367446484901116939781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34239156595313201489253041 25679367446484901116939781)
                  ·
                    refine ⟨4814881396215918959426209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25679367446484901116939781 4814881396215918959426209)
                    ·
                      refine ⟨3611161047161939219569657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4814881396215918959426209 3611161047161939219569657)
                      ·
                        rfl

theorem cell23_7032711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_7032711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032711 prefixEnd_7032711 := by exact prefixLift 7032711
  have htrace : WordTrace (prefixWord ++ tailWord_7032711) baseStart_7032711 baseEnd_7032711 := by
    simpa [prefixWord, tailWord_7032711, baseEnd_7032711] using wordTrace_append hprefix tailTrace_7032711
  have hstable : (prefixWord ++ tailWord_7032711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032711).length < 2 ^ (prefixWord ++ tailWord_7032711).sum := by decide
  have hdescent : baseEnd_7032711 < baseStart_7032711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032728 : List Nat := [2, 1, 2, 6, 1, 2, 1, 1, 2, 1, 4]
def baseStart_7032728 : Nat := 118140960795 + 7032728 * 2 ^ 59
def prefixEnd_7032728 : Nat := 4983230072969 + 3 ^ 40 * 7032728 * 2
def baseEnd_7032728 : Nat := 3611169776333065653057079

theorem tailTrace_7032728 : CollatzResearch.WordTrace tailWord_7032728 prefixEnd_7032728 3611169776333065653057079 := by
  unfold tailWord_7032728
  simp only [CollatzResearch.WordTrace]
  refine ⟨128252331432817512581753419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171003108577090016775671225 128252331432817512581753419)
  ·
    refine ⟨192378497149226268872630129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128252331432817512581753419 192378497149226268872630129)
    ·
      refine ⟨144283872861919701654472597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192378497149226268872630129 144283872861919701654472597)
      ·
        refine ⟨6763306540402486015053403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 144283872861919701654472597 6763306540402486015053403)
        ·
          refine ⟨10144959810603729022580105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6763306540402486015053403 10144959810603729022580105)
          ·
            refine ⟨7608719857952796766935079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10144959810603729022580105 7608719857952796766935079)
            ·
              refine ⟨11413079786929195150402619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7608719857952796766935079 11413079786929195150402619)
              ·
                refine ⟨17119619680393792725603929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11413079786929195150402619 17119619680393792725603929)
                ·
                  refine ⟨12839714760295344544202947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17119619680393792725603929 12839714760295344544202947)
                  ·
                    refine ⟨19259572140443016816304421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12839714760295344544202947 19259572140443016816304421)
                    ·
                      refine ⟨3611169776333065653057079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19259572140443016816304421 3611169776333065653057079)
                      ·
                        rfl

theorem cell23_7032728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_7032728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032728 prefixEnd_7032728 := by exact prefixLift 7032728
  have htrace : WordTrace (prefixWord ++ tailWord_7032728) baseStart_7032728 baseEnd_7032728 := by
    simpa [prefixWord, tailWord_7032728, baseEnd_7032728] using wordTrace_append hprefix tailTrace_7032728
  have hstable : (prefixWord ++ tailWord_7032728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032728).length < 2 ^ (prefixWord ++ tailWord_7032728).sum := by decide
  have hdescent : baseEnd_7032728 < baseStart_7032728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032761 : List Nat := [1, 2, 1, 4, 2, 1, 4, 1, 3, 1, 3]
def baseStart_7032761 : Nat := 118140960795 + 7032761 * 2 ^ 59
def prefixEnd_7032761 : Nat := 4983230072969 + 3 ^ 40 * 7032761 * 2
def baseEnd_7032761 : Nat := 3611186721194664023944427

theorem tailTrace_7032761 : CollatzResearch.WordTrace tailWord_7032761 prefixEnd_7032761 3611186721194664023944427 := by
  unfold tailWord_7032761
  simp only [CollatzResearch.WordTrace]
  refine ⟨256505866474515471799458137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171003910983010314532972091 256505866474515471799458137)
  ·
    refine ⟨192379399855886603849593603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256505866474515471799458137 192379399855886603849593603)
    ·
      refine ⟨288569099783829905774390405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192379399855886603849593603 288569099783829905774390405)
      ·
        refine ⟨54106706209468107332698201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 288569099783829905774390405 54106706209468107332698201)
        ·
          refine ⟨40580029657101080499523651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54106706209468107332698201 40580029657101080499523651)
          ·
            refine ⟨60870044485651620749285477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40580029657101080499523651 60870044485651620749285477)
            ·
              refine ⟨11413133341059678890491027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60870044485651620749285477 11413133341059678890491027)
              ·
                refine ⟨17119700011589518335736541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11413133341059678890491027 17119700011589518335736541)
                ·
                  refine ⟨6419887504346069375901203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17119700011589518335736541 6419887504346069375901203)
                  ·
                    refine ⟨9629831256519104063851805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6419887504346069375901203 9629831256519104063851805)
                    ·
                      refine ⟨3611186721194664023944427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9629831256519104063851805 3611186721194664023944427)
                      ·
                        rfl

theorem cell23_7032761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_7032761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032761 prefixEnd_7032761 := by exact prefixLift 7032761
  have htrace : WordTrace (prefixWord ++ tailWord_7032761) baseStart_7032761 baseEnd_7032761 := by
    simpa [prefixWord, tailWord_7032761, baseEnd_7032761] using wordTrace_append hprefix tailTrace_7032761
  have hstable : (prefixWord ++ tailWord_7032761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032761).length < 2 ^ (prefixWord ++ tailWord_7032761).sum := by decide
  have hdescent : baseEnd_7032761 < baseStart_7032761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032784 : List Nat := [2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 4]
def baseStart_7032784 : Nat := 118140960795 + 7032784 * 2 ^ 59
def prefixEnd_7032784 : Nat := 4983230072969 + 3 ^ 40 * 7032784 * 2
def baseEnd_7032784 : Nat := 3611198531249717433956821

theorem tailTrace_7032784 : CollatzResearch.WordTrace tailWord_7032784 prefixEnd_7032784 3611198531249717433956821 := by
  unfold tailWord_7032784
  simp only [CollatzResearch.WordTrace]
  refine ⟨128253352676716073363772703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171004470235621431151696937 128253352676716073363772703)
  ·
    refine ⟨192380029015074110045659055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128253352676716073363772703 192380029015074110045659055)
    ·
      refine ⟨288570043522611165068488583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192380029015074110045659055 288570043522611165068488583)
      ·
        refine ⟨432855065283916747602732875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288570043522611165068488583 432855065283916747602732875)
        ·
          refine ⟨649282597925875121404099313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432855065283916747602732875 649282597925875121404099313)
          ·
            refine ⟨486961948444406341053074485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 649282597925875121404099313 486961948444406341053074485)
            ·
              refine ⟨45652682666663094473725733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 486961948444406341053074485 45652682666663094473725733)
              ·
                refine ⟨8559877999999330213823575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45652682666663094473725733 8559877999999330213823575)
                ·
                  refine ⟨12839816999998995320735363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8559877999999330213823575 12839816999998995320735363)
                  ·
                    refine ⟨19259725499998492981103045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12839816999998995320735363 19259725499998492981103045)
                    ·
                      refine ⟨3611198531249717433956821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19259725499998492981103045 3611198531249717433956821)
                      ·
                        rfl

theorem cell23_7032784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 4].length) (baseStart_7032784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032784 prefixEnd_7032784 := by exact prefixLift 7032784
  have htrace : WordTrace (prefixWord ++ tailWord_7032784) baseStart_7032784 baseEnd_7032784 := by
    simpa [prefixWord, tailWord_7032784, baseEnd_7032784] using wordTrace_append hprefix tailTrace_7032784
  have hstable : (prefixWord ++ tailWord_7032784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032784).length < 2 ^ (prefixWord ++ tailWord_7032784).sum := by decide
  have hdescent : baseEnd_7032784 < baseStart_7032784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032801 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 5, 2, 2]
def baseStart_7032801 : Nat := 118140960795 + 7032801 * 2 ^ 59
def prefixEnd_7032801 : Nat := 4983230072969 + 3 ^ 40 * 7032801 * 2
def baseEnd_7032801 : Nat := 3611207260420843867444243

theorem tailTrace_7032801 : CollatzResearch.WordTrace tailWord_7032801 prefixEnd_7032801 3611207260420843867444243 := by
  unfold tailWord_7032801
  simp only [CollatzResearch.WordTrace]
  refine ⟨256507325394370558630914257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171004883596247039087276171 256507325394370558630914257)
  ·
    refine ⟨192380494045777918973185693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256507325394370558630914257 192380494045777918973185693)
    ·
      refine ⟨72142685267166719614944635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192380494045777918973185693 72142685267166719614944635)
      ·
        refine ⟨108214027900750079422416953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72142685267166719614944635 108214027900750079422416953)
        ·
          refine ⟨81160520925562559566812715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108214027900750079422416953 81160520925562559566812715)
          ·
            refine ⟨121740781388343839350219073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81160520925562559566812715 121740781388343839350219073)
            ·
              refine ⟨91305586041257879512664305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121740781388343839350219073 91305586041257879512664305)
              ·
                refine ⟨68479189530943409634498229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91305586041257879512664305 68479189530943409634498229)
                ·
                  refine ⟨6419924018525944653234209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68479189530943409634498229 6419924018525944653234209)
                  ·
                    refine ⟨4814943013894458489925657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6419924018525944653234209 4814943013894458489925657)
                    ·
                      refine ⟨3611207260420843867444243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4814943013894458489925657 3611207260420843867444243)
                      ·
                        rfl

theorem cell23_7032801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 2, 2].length) (baseStart_7032801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032801 prefixEnd_7032801 := by exact prefixLift 7032801
  have htrace : WordTrace (prefixWord ++ tailWord_7032801) baseStart_7032801 baseEnd_7032801 := by
    simpa [prefixWord, tailWord_7032801, baseEnd_7032801] using wordTrace_append hprefix tailTrace_7032801
  have hstable : (prefixWord ++ tailWord_7032801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032801).length < 2 ^ (prefixWord ++ tailWord_7032801).sum := by decide
  have hdescent : baseEnd_7032801 < baseStart_7032801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032804 : List Nat := [2, 3, 1, 1, 1, 1, 6, 1, 1, 1, 5]
def baseStart_7032804 : Nat := 118140960795 + 7032804 * 2 ^ 59
def prefixEnd_7032804 : Nat := 4983230072969 + 3 ^ 40 * 7032804 * 2
def baseEnd_7032804 : Nat := 3611208800862807355706729

theorem tailTrace_7032804 : CollatzResearch.WordTrace tailWord_7032804 prefixEnd_7032804 3611208800862807355706729 := by
  unfold tailWord_7032804
  simp only [CollatzResearch.WordTrace]
  refine ⟨128253717406679845071636733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171004956542239793428848977 128253717406679845071636733)
  ·
    refine ⟨48095144027504941901863775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128253717406679845071636733 48095144027504941901863775)
    ·
      refine ⟨72142716041257412852795663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48095144027504941901863775 72142716041257412852795663)
      ·
        refine ⟨108214074061886119279193495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72142716041257412852795663 108214074061886119279193495)
        ·
          refine ⟨162321111092829178918790243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108214074061886119279193495 162321111092829178918790243)
          ·
            refine ⟨243481666639243768378185365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162321111092829178918790243 243481666639243768378185365)
            ·
              refine ⟨11413203123714551642727439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 243481666639243768378185365 11413203123714551642727439)
              ·
                refine ⟨17119804685571827464091159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11413203123714551642727439 17119804685571827464091159)
                ·
                  refine ⟨25679707028357741196136739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17119804685571827464091159 25679707028357741196136739)
                  ·
                    refine ⟨38519560542536611794205109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25679707028357741196136739 38519560542536611794205109)
                    ·
                      refine ⟨3611208800862807355706729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38519560542536611794205109 3611208800862807355706729)
                      ·
                        rfl

theorem cell23_7032804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_7032804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032804 prefixEnd_7032804 := by exact prefixLift 7032804
  have htrace : WordTrace (prefixWord ++ tailWord_7032804) baseStart_7032804 baseEnd_7032804 := by
    simpa [prefixWord, tailWord_7032804, baseEnd_7032804] using wordTrace_append hprefix tailTrace_7032804
  have hstable : (prefixWord ++ tailWord_7032804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032804).length < 2 ^ (prefixWord ++ tailWord_7032804).sum := by decide
  have hdescent : baseEnd_7032804 < baseStart_7032804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032814 : List Nat := [4, 1, 2, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_7032814 : Nat := 118140960795 + 7032814 * 2 ^ 59
def prefixEnd_7032814 : Nat := 4983230072969 + 3 ^ 40 * 7032814 * 2
def baseEnd_7032814 : Nat := 3611213935669352316581683

theorem tailTrace_7032814 : CollatzResearch.WordTrace tailWord_7032814 prefixEnd_7032814 3611213935669352316581683 := by
  unfold tailWord_7032814
  simp only [CollatzResearch.WordTrace]
  refine ⟨32063474942915432731392187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171005199695548974567424997 32063474942915432731392187)
  ·
    refine ⟨48095212414373149097088281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32063474942915432731392187 48095212414373149097088281)
    ·
      refine ⟨36071409310779861822816211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48095212414373149097088281 36071409310779861822816211)
      ·
        refine ⟨54107113966169792734224317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36071409310779861822816211 54107113966169792734224317)
        ·
          refine ⟨20290167737313672275334119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54107113966169792734224317 20290167737313672275334119)
          ·
            refine ⟨30435251605970508413001179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20290167737313672275334119 30435251605970508413001179)
            ·
              refine ⟨45652877408955762619501769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30435251605970508413001179 45652877408955762619501769)
              ·
                refine ⟨34239658056716821964626327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45652877408955762619501769 34239658056716821964626327)
                ·
                  refine ⟨51359487085075232946939491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34239658056716821964626327 51359487085075232946939491)
                  ·
                    refine ⟨77039230627612849420409237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51359487085075232946939491 77039230627612849420409237)
                    ·
                      refine ⟨3611213935669352316581683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77039230627612849420409237 3611213935669352316581683)
                      ·
                        rfl

theorem cell23_7032814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_7032814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032814 prefixEnd_7032814 := by exact prefixLift 7032814
  have htrace : WordTrace (prefixWord ++ tailWord_7032814) baseStart_7032814 baseEnd_7032814 := by
    simpa [prefixWord, tailWord_7032814, baseEnd_7032814] using wordTrace_append hprefix tailTrace_7032814
  have hstable : (prefixWord ++ tailWord_7032814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032814).length < 2 ^ (prefixWord ++ tailWord_7032814).sum := by decide
  have hdescent : baseEnd_7032814 < baseStart_7032814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032845 : List Nat := [1, 7, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_7032845 : Nat := 118140960795 + 7032845 * 2 ^ 59
def prefixEnd_7032845 : Nat := 4983230072969 + 3 ^ 40 * 7032845 * 2
def baseEnd_7032845 : Nat := 1203743284523213898431347

theorem tailTrace_7032845 : CollatzResearch.WordTrace tailWord_7032845 prefixEnd_7032845 1203743284523213898431347 := by
  unfold tailWord_7032845
  simp only [CollatzResearch.WordTrace]
  refine ⟨256508930206211154145515989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171005953470807436097010659 256508930206211154145515989)
  ·
    refine ⟨6011928051708073925285531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 256508930206211154145515989 6011928051708073925285531)
    ·
      refine ⟨9017892077562110887928297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6011928051708073925285531 9017892077562110887928297)
      ·
        refine ⟨6763419058171583165946223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9017892077562110887928297 6763419058171583165946223)
        ·
          refine ⟨10145128587257374748919335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6763419058171583165946223 10145128587257374748919335)
          ·
            refine ⟨15217692880886062123379003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10145128587257374748919335 15217692880886062123379003)
            ·
              refine ⟨22826539321329093185068505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15217692880886062123379003 22826539321329093185068505)
              ·
                refine ⟨17119904490996819888801379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22826539321329093185068505 17119904490996819888801379)
                ·
                  refine ⟨25679856736495229833202069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17119904490996819888801379 25679856736495229833202069)
                  ·
                    refine ⟨1203743284523213898431347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25679856736495229833202069 1203743284523213898431347)
                    ·
                      rfl

theorem cell23_7032845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_7032845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032845 prefixEnd_7032845 := by exact prefixLift 7032845
  have htrace : WordTrace (prefixWord ++ tailWord_7032845) baseStart_7032845 baseEnd_7032845 := by
    simpa [prefixWord, tailWord_7032845, baseEnd_7032845] using wordTrace_append hprefix tailTrace_7032845
  have hstable : (prefixWord ++ tailWord_7032845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032845).length < 2 ^ (prefixWord ++ tailWord_7032845).sum := by decide
  have hdescent : baseEnd_7032845 < baseStart_7032845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032852 : List Nat := [2, 4, 3, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_7032852 : Nat := 118140960795 + 7032852 * 2 ^ 59
def prefixEnd_7032852 : Nat := 4983230072969 + 3 ^ 40 * 7032852 * 2
def baseEnd_7032852 : Nat := 3611233447934223167906509

theorem tailTrace_7032852 : CollatzResearch.WordTrace tailWord_7032852 prefixEnd_7032852 3611233447934223167906509 := by
  unfold tailWord_7032852
  simp only [CollatzResearch.WordTrace]
  refine ⟨128254592758592897170510405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171006123678123862894013873 128254592758592897170510405)
  ·
    refine ⟨24047736142236168219470701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128254592758592897170510405 24047736142236168219470701)
    ·
      refine ⟨9017901053338563082301513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24047736142236168219470701 9017901053338563082301513)
      ·
        refine ⟨6763425790003922311726135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9017901053338563082301513 6763425790003922311726135)
        ·
          refine ⟨10145138685005883467589203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6763425790003922311726135 10145138685005883467589203)
          ·
            refine ⟨15217708027508825201383805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10145138685005883467589203 15217708027508825201383805)
            ·
              refine ⟨5706640510315809450518927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15217708027508825201383805 5706640510315809450518927)
              ·
                refine ⟨8559960765473714175778391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5706640510315809450518927 8559960765473714175778391)
                ·
                  refine ⟨12839941148210571263667587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8559960765473714175778391 12839941148210571263667587)
                  ·
                    refine ⟨19259911722315856895501381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12839941148210571263667587 19259911722315856895501381)
                    ·
                      refine ⟨3611233447934223167906509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19259911722315856895501381 3611233447934223167906509)
                      ·
                        rfl

theorem cell23_7032852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_7032852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032852 prefixEnd_7032852 := by exact prefixLift 7032852
  have htrace : WordTrace (prefixWord ++ tailWord_7032852) baseStart_7032852 baseEnd_7032852 := by
    simpa [prefixWord, tailWord_7032852, baseEnd_7032852] using wordTrace_append hprefix tailTrace_7032852
  have hstable : (prefixWord ++ tailWord_7032852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032852).length < 2 ^ (prefixWord ++ tailWord_7032852).sum := by decide
  have hdescent : baseEnd_7032852 < baseStart_7032852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032855 : List Nat := [1, 1, 3, 5, 2, 1, 3, 1, 1, 2, 3]
def baseStart_7032855 : Nat := 118140960795 + 7032855 * 2 ^ 59
def prefixEnd_7032855 : Nat := 4983230072969 + 3 ^ 40 * 7032855 * 2
def baseEnd_7032855 : Nat := 3611234988376186656168995

theorem tailTrace_7032855 : CollatzResearch.WordTrace tailWord_7032855 prefixEnd_7032855 3611234988376186656168995 := by
  unfold tailWord_7032855
  simp only [CollatzResearch.WordTrace]
  refine ⟨256509294936174925853380019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171006196624116617235586679 256509294936174925853380019)
  ·
    refine ⟨384763942404262388780070029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256509294936174925853380019 384763942404262388780070029)
    ·
      refine ⟨144286478401598395792526261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384763942404262388780070029 144286478401598395792526261)
      ·
        refine ⟨13526857350149849605549337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144286478401598395792526261 13526857350149849605549337)
        ·
          refine ⟨10145143012612387204162003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13526857350149849605549337 10145143012612387204162003)
          ·
            refine ⟨15217714518918580806243005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10145143012612387204162003 15217714518918580806243005)
            ·
              refine ⟨5706642944594467802341127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15217714518918580806243005 5706642944594467802341127)
              ·
                refine ⟨8559964416891701703511691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5706642944594467802341127 8559964416891701703511691)
                ·
                  refine ⟨12839946625337552555267537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8559964416891701703511691 12839946625337552555267537)
                  ·
                    refine ⟨9629959969003164416450653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12839946625337552555267537 9629959969003164416450653)
                    ·
                      refine ⟨3611234988376186656168995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9629959969003164416450653 3611234988376186656168995)
                      ·
                        rfl

theorem cell23_7032855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_7032855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032855 prefixEnd_7032855 := by exact prefixLift 7032855
  have htrace : WordTrace (prefixWord ++ tailWord_7032855) baseStart_7032855 baseEnd_7032855 := by
    simpa [prefixWord, tailWord_7032855, baseEnd_7032855] using wordTrace_append hprefix tailTrace_7032855
  have hstable : (prefixWord ++ tailWord_7032855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032855).length < 2 ^ (prefixWord ++ tailWord_7032855).sum := by decide
  have hdescent : baseEnd_7032855 < baseStart_7032855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032878 : List Nat := [4, 1, 3, 1, 1, 2, 1, 2, 3, 3, 2]
def baseStart_7032878 : Nat := 118140960795 + 7032878 * 2 ^ 59
def prefixEnd_7032878 : Nat := 4983230072969 + 3 ^ 40 * 7032878 * 2
def baseEnd_7032878 : Nat := 3611246798431240066181389

theorem tailTrace_7032878 : CollatzResearch.WordTrace tailWord_7032878 prefixEnd_7032878 3611246798431240066181389 := by
  unfold tailWord_7032878
  simp only [CollatzResearch.WordTrace]
  refine ⟨32063766726886450097683411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171006755876727733854311525 32063766726886450097683411)
  ·
    refine ⟨48095650090329675146525117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32063766726886450097683411 48095650090329675146525117)
    ·
      refine ⟨18035868783873628179946919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48095650090329675146525117 18035868783873628179946919)
      ·
        refine ⟨27053803175810442269920379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18035868783873628179946919 27053803175810442269920379)
        ·
          refine ⟨40580704763715663404880569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27053803175810442269920379 40580704763715663404880569)
          ·
            refine ⟨30435528572786747553660427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40580704763715663404880569 30435528572786747553660427)
            ·
              refine ⟨45653292859180121330490641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30435528572786747553660427 45653292859180121330490641)
              ·
                refine ⟨34239969644385090997867981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45653292859180121330490641 34239969644385090997867981)
                ·
                  refine ⟨12839988616644409124200493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34239969644385090997867981 12839988616644409124200493)
                  ·
                    refine ⟨4814995731241653421575185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12839988616644409124200493 4814995731241653421575185)
                    ·
                      refine ⟨3611246798431240066181389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4814995731241653421575185 3611246798431240066181389)
                      ·
                        rfl

theorem cell23_7032878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_7032878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032878 prefixEnd_7032878 := by exact prefixLift 7032878
  have htrace : WordTrace (prefixWord ++ tailWord_7032878) baseStart_7032878 baseEnd_7032878 := by
    simpa [prefixWord, tailWord_7032878, baseEnd_7032878] using wordTrace_append hprefix tailTrace_7032878
  have hstable : (prefixWord ++ tailWord_7032878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032878).length < 2 ^ (prefixWord ++ tailWord_7032878).sum := by decide
  have hdescent : baseEnd_7032878 < baseStart_7032878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7032918 : List Nat := [5, 2, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_7032918 : Nat := 118140960795 + 7032918 * 2 ^ 59
def prefixEnd_7032918 : Nat := 4983230072969 + 3 ^ 40 * 7032918 * 2
def baseEnd_7032918 : Nat := 1203755779219139969893735

theorem tailTrace_7032918 : CollatzResearch.WordTrace tailWord_7032918 prefixEnd_7032918 1203755779219139969893735 := by
  unfold tailWord_7032918
  simp only [CollatzResearch.WordTrace]
  refine ⟨16031974545934167975807713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171007728489964458408615605 16031974545934167975807713)
  ·
    refine ⟨12023980909450625981855785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16031974545934167975807713 12023980909450625981855785)
    ·
      refine ⟨9017985682087969486391839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12023980909450625981855785 9017985682087969486391839)
      ·
        refine ⟨13526978523131954229587759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9017985682087969486391839 13526978523131954229587759)
        ·
          refine ⟨20290467784697931344381639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13526978523131954229587759 20290467784697931344381639)
          ·
            refine ⟨30435701677046897016572459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20290467784697931344381639 30435701677046897016572459)
            ·
              refine ⟨45653552515570345524858689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30435701677046897016572459 45653552515570345524858689)
              ·
                refine ⟨34240164386677759143644017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45653552515570345524858689 34240164386677759143644017)
                ·
                  refine ⟨25680123290008319357733013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34240164386677759143644017 25680123290008319357733013)
                  ·
                    refine ⟨1203755779219139969893735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25680123290008319357733013 1203755779219139969893735)
                    ·
                      rfl

theorem cell23_7032918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_7032918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7032918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7032918 prefixEnd_7032918 := by exact prefixLift 7032918
  have htrace : WordTrace (prefixWord ++ tailWord_7032918) baseStart_7032918 baseEnd_7032918 := by
    simpa [prefixWord, tailWord_7032918, baseEnd_7032918] using wordTrace_append hprefix tailTrace_7032918
  have hstable : (prefixWord ++ tailWord_7032918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7032918).length < 2 ^ (prefixWord ++ tailWord_7032918).sum := by decide
  have hdescent : baseEnd_7032918 < baseStart_7032918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7032918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
